// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import java.lang.ref.WeakReference;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.WeakHashMap;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.util.AbstractExecutionUtils;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Triple;

/**
 * Class of operators for abstract updates (in the sense of Abstract Execution),
 * i.e., updates of the form "U(LOCSET1 := LOCSET2)", where LOCSET1/2 are
 * location sets. There is one such operator for every left hand side "LOCSET1".
 * Each of these operator is unary, accepting a single argument "LOCSET2".
 * Comparable to an {@link ElementaryUpdate}.
 */
public final class AbstractUpdate extends AbstractSortedOperator {

    private static final WeakHashMap<AbstractPlaceholderStatement, //
            WeakHashMap<Term, WeakReference<AbstractUpdate>>> INSTANCES = //
                    new WeakHashMap<>();
    private static final Map<KeYJavaType, LocationVariable> SELF_VAR_MAP = new LinkedHashMap<>();

    private final AbstractPlaceholderStatement phs;
    //@formatter:off
    /* Invariant: lhs is a LocSet union of
     * - singletonPV functions applied to location variables
     * - Skolem LocSet functions
     * - Normal LocSet singletons (not yet supported)
     * - Either of the above wrapped in a hasTo function
     */
    //@formatter:on
    /**
     * The left-hand side {@link Term} for this {@link AbstractUpdate}.
     */
    private final Term lhs;

    /**
     * Assignables that may be assigned. Location variables or Skolem LocSet
     * functions. Unmodifiable.
     */
    private final Set<Operator> maybeAssignables;

    /**
     * Assignables that have to be assigned. Location variables or Skolem LocSet
     * functions. Unmodifiable.
     */
    private final Set<Operator> haveToAssignables;

    /**
     * Assignables, both "has-to" and "maybe". Location variables wrapped in the
     * singletonPV function, or Skolem LocSet functions, where both may be
     * wrapped in a hasTo function if they are "has-to". Unmodifiable. Use
     * {@link #getMaybeAssignables()} or {@link #getHasToAssignables()} to get
     * easier access to the two different sorts of assignables.
     */
    private final Set<Term> allAssignables;

    private AbstractUpdate(final AbstractPlaceholderStatement phs,
            final Term lhs, final Services services) {
        super(new Name("U_" + phs.getId() + "(" + lhs + ")"),
                new Sort[] {
                        services.getTypeConverter().getSetLDT().targetSort() },
                Sort.UPDATE, false);

        this.lhs = normalizeLHSSelfTerms(lhs, services);

        final Triple<Set<Term>, Set<Operator>, Set<Operator>> disassembledLHS = //
                disassembleLHS(lhs, services);
        this.allAssignables = disassembledLHS.first;
        this.maybeAssignables = disassembledLHS.second;
        this.haveToAssignables = disassembledLHS.third;

        this.phs = phs;
        assert lhs.sort() == services.getTypeConverter().getLocSetLDT()
                .targetSort();
    }

    private static Term normalizeLHSSelfTerms(final Term lhs,
            final Services services) {
        final Optional<LocationVariable> maybeSelfVar = extractSelfVar(lhs);
        if (maybeSelfVar.isPresent()) {
            final LocationVariable selfVar = maybeSelfVar.get();
            final KeYJavaType kjt = selfVar.getKeYJavaType();
            if (!SELF_VAR_MAP.containsKey(kjt)) {
                SELF_VAR_MAP.put(kjt, selfVar);
            } else {
                final Map<ProgramVariable, ProgramVariable> map = new LinkedHashMap<>();
                map.put(selfVar, SELF_VAR_MAP.get(kjt));
                final ProgVarReplacer pvr = new ProgVarReplacer(map, services);
                return pvr.replace(lhs);
            }
        }

        return lhs;
    }

    private static Optional<LocationVariable> extractSelfVar(Term lhs) {
        final OpCollector opColl = new OpCollector();
        lhs.execPostOrder(opColl);
        return opColl.ops().stream().filter(LocationVariable.class::isInstance)
                .map(LocationVariable.class::cast)
                .filter(lv -> lv.name().equals(new Name("self"))).findFirst();
    }

    /**
     * @param lhs
     *            The left-hand side to disassemble.
     * @param services
     *            The {@link Services} object.
     * @return A pair of (1) all assignable terms, (2) the maybe assignables and
     *         (3) the have-to assignables. Both sets are immutable.
     */
    private static Triple<Set<Term>, Set<Operator>, Set<Operator>> disassembleLHS(
            Term lhs, Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final Function union = locSetLDT.getUnion();
        final Function hasToFunc = locSetLDT.getHasTo();
        final java.util.function.Function<? super Term, ? extends Operator> mapper = //
                AbstractExecutionUtils.locSetElemTermsToOpMapper(services);

        final Set<Term> unionElems = MiscTools.dissasembleSetTerm(lhs, union);
        final Set<Operator> maybeAssignables = unionElems.stream()
                .filter(t -> t.op() != hasToFunc).map(mapper)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
        final Set<Operator> haveToAssignables = unionElems.stream()
                .filter(t -> t.op() == hasToFunc).map(t -> t.sub(0)).map(mapper)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        return new Triple<>(
                Collections.unmodifiableSet(unionElems.stream()
                        .map(t -> AbstractExecutionUtils
                                .preprocessLocSetElemTerms(t, services))
                        .collect(Collectors
                                .toCollection(() -> new LinkedHashSet<>()))),
                Collections.unmodifiableSet(maybeAssignables),
                Collections.unmodifiableSet(haveToAssignables));
    }

    /**
     * Returns the abstract update operator for the passed left hand side.
     */
    public static AbstractUpdate getInstance(AbstractPlaceholderStatement phs,
            Term lhs, Services services) {
        if (INSTANCES.get(phs) == null) {
            INSTANCES.put(phs, new WeakHashMap<>());
        }

        WeakReference<AbstractUpdate> result = INSTANCES.get(phs).get(lhs);
        if (result == null || result.get() == null) {
            result = new WeakReference<AbstractUpdate>(
                    new AbstractUpdate(phs, lhs, services));
            INSTANCES.get(phs).put(lhs, result);
        }

        return result.get();
    }

    public AbstractPlaceholderStatement getAbstractPlaceholderStatement() {
        return this.phs;
    }

    /**
     * Returns the left hand side of this abstract update operator.
     */
    public Term lhs() {
        return this.lhs;
    }

    public String getUpdateName() {
        /*
         * TODO (DS, 2019-01-03): There might be collisions here, ignoring for
         * now...
         */
        return "U_" + phs.getId();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * this.lhs.hashCode() + 27 * this.phs.hashCode();
    }

    /**
     * Assignables, both "has-to" and "maybe". Location variables wrapped in the
     * singletonPV function, or Skolem LocSet functions, where both may be
     * wrapped in a hasTo function if they are "has-to". Unmodifiable. Use
     * {@link #getMaybeAssignables()} or {@link #getHasToAssignables()} to get
     * easier access to the two different sorts of assignables.
     *
     * @return All assignables.
     */
    public Set<Term> getAllAssignables() {
        return allAssignables;
    }

    /**
     * Assignables that may be assigned. Location variables or Skolem LocSet
     * functions. Set is immutable.
     *
     * @return The elements of the assignables union of this abstract update
     *         that may be assigned.
     */
    public Set<Operator> getMaybeAssignables() {
        return maybeAssignables;
    }

    /**
     * Assignables that have to be assigned. Location variables or Skolem LocSet
     * functions. Set is immutable.
     *
     * @return The elements of the assignables union of this abstract update
     *         that have to be assigned.
     */
    public Set<Operator> getHasToAssignables() {
        return haveToAssignables;
    }
}