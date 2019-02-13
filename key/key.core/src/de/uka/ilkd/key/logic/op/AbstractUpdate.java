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
import java.util.Set;
import java.util.WeakHashMap;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

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
     * Assignables that may be assigned. Terms of singletonPV functions applied
     * to location variables or Skolem LocSet functions. Unmodifiable.
     */
    private final Set<Term> maybeAssignables;

    /**
     * Assignables that have to be assigned. Terms of singletonPV functions
     * applied to location variables or Skolem LocSet functions. Unmodifiable.
     */
    private final Set<Term> haveToAssignables;

    private AbstractUpdate(AbstractPlaceholderStatement phs, Term lhs,
            LocSetLDT locSetLDT, SetLDT setLDT) {
        super(new Name("U_" + phs.getId() + "(" + lhs + ")"),
                new Sort[] { setLDT.targetSort() }, Sort.UPDATE, false);
        this.lhs = lhs;

        final Pair<Set<Term>, Set<Term>> disassembledLHS = //
                disassembleLHS(lhs, locSetLDT);
        this.maybeAssignables = disassembledLHS.first;
        this.haveToAssignables = disassembledLHS.second;

        this.phs = phs;
        assert lhs.sort() == locSetLDT.targetSort();
    }

    /**
     * @param lhs
     *            The left-hand side to disassemble.
     * @param locSetLDT
     *            The {@link LocSetLDT} theory.
     * @return A pair of (1) the maybe assignables and (2) the have-to
     *         assignables. Both sets are immutable.
     */
    private static Pair<Set<Term>, Set<Term>> disassembleLHS(Term lhs,
            LocSetLDT locSetLDT) {
        final Function union = locSetLDT.getUnion();
        final Function hasToFunc = locSetLDT.getHasTo();

        final Set<Term> unionElems = MiscTools.dissasembleSetTerm(lhs, union);

        final Set<Term> maybeAssignables = unionElems.stream()
                .filter(t -> t.op() != hasToFunc)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
        final Set<Term> haveToAssignables = unionElems.stream()
                .filter(t -> t.op() == hasToFunc).map(t -> t.sub(0))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        return new Pair<>(Collections.unmodifiableSet(maybeAssignables),
                Collections.unmodifiableSet(haveToAssignables));
    }

    /**
     * Returns the abstract update operator for the passed left hand side.
     */
    public static AbstractUpdate getInstance(AbstractPlaceholderStatement phs,
            Term lhs, LocSetLDT locSetLDT, SetLDT setLDT) {
        if (INSTANCES.get(phs) == null) {
            INSTANCES.put(phs, new WeakHashMap<>());
        }

        WeakReference<AbstractUpdate> result = INSTANCES.get(phs).get(lhs);
        if (result == null || result.get() == null) {
            result = new WeakReference<AbstractUpdate>(
                    new AbstractUpdate(phs, lhs, locSetLDT, setLDT));
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
     * Assignables that may be assigned. Terms of singletonPV functions applied
     * to location variables or Skolem LocSet functions.
     *
     * @return The elements of the assignables union of this abstract update
     *         that may be assigned.
     */
    public Set<Term> getMaybeAssignables() {
        return maybeAssignables;
    }

    /**
     * Assignables that have to be assigned. Terms of singletonPV functions
     * applied to location variables or Skolem LocSet functions.
     *
     * @return The elements of the assignables union of this abstract update
     *         that have to be assigned.
     */
    public Set<Term> getHasToAssignables() {
        return haveToAssignables;
    }
}