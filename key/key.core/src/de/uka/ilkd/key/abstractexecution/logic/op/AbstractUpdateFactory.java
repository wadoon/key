// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.logic.op;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.ArrayLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.EmptyLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.FieldLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.RigidRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Factory class for {@link AbstractUpdate}s and {@link AbstractUpdate} LHSs /
 * RHSs.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractUpdateFactory {
    private final HashMap<String, //
            HashMap<Integer, AbstractUpdate>> abstractUpdateInstances = //
                    new LinkedHashMap<>();

    /**
     * Constructor. NOTE: You should not use this constructor, but instead
     * access {@link Services#abstractUpdateFactory()}, since this factory
     * caches {@link AbstractUpdate}s. You'll probably face incompleteness
     * issues if you don't follow this rule.
     */
    public AbstractUpdateFactory() {
    }

    /**
     * Returns abstract update operator for the passed
     * {@link AbstractPlaceholderStatement} and left-hand side.
     *
     * @param phs
     *            The {@link AbstractPlaceholderStatement} for which this
     *            {@link AbstractUpdate} should be created.
     * @param lhs
     *            The update's left-hand side. Should be a {@link SetLDT} term.
     * @param ec
     *            The {@link ExecutionContext} for the
     *            {@link AbstractPlaceholderStatement}.
     * @param services
     *            The {@link Services} object.
     * @return The {@link AbstractUpdate} for the given
     *         {@link AbstractPlaceholderStatement} and left-hand side.
     */
    public AbstractUpdate getInstance(AbstractPlaceholderStatement phs,
            Term lhs, ExecutionContext ec, Services services) {
        final LinkedHashSet<AbstrUpdateLHS> assignables = //
                abstractUpdateLocsFromUnionTerm(lhs, ec, services).stream()
                        .map(AbstrUpdateLHS.class::cast).collect(Collectors
                                .toCollection(() -> new LinkedHashSet<>()));

        return getInstance(phs, assignables, ec, services);
    }

    /**
     * Returns abstract update operator for the passed
     * {@link AbstractPlaceholderStatement} and left-hand side.
     *
     * @param phs
     *            The {@link AbstractPlaceholderStatement} for which this
     *            {@link AbstractUpdate} should be created.
     * @param assignables
     *            The update's left-hand side.
     * @param ec
     *            The {@link ExecutionContext} in which the
     *            {@link AbstractUpdate} is generated.
     * @param services
     *            The {@link Services} object.
     * @return The {@link AbstractUpdate} for the given
     *         {@link AbstractPlaceholderStatement} and left-hand side.
     */
    public AbstractUpdate getInstance(AbstractPlaceholderStatement phs,
            Set<AbstrUpdateLHS> assignables, ExecutionContext ec,
            Services services) {
        final String phsID = phs.getId();
        if (abstractUpdateInstances.get(phsID) == null) {
            abstractUpdateInstances.put(phsID, new LinkedHashMap<>());
        }

        final int assgnHashCode = assignables.hashCode();
        AbstractUpdate result = //
                abstractUpdateInstances.get(phsID).get(assgnHashCode);
        if (result == null) {
            result = new AbstractUpdate(phs, assignables, ec, services);
            abstractUpdateInstances.get(phsID).put(assgnHashCode, result);
        }

        return result;
    }

    /**
     * Returns a new abstract update for the same
     * {@link AbstractPlaceholderStatement}, but with the supplied assignables.
     *
     * @param abstrUpd
     *            The original {@link AbstractUpdate}.
     * @param newAssignables
     *            The new assignables (left-hand sides).
     * @return A new {@link AbstractUpdate} for the same
     *         {@link AbstractPlaceholderStatement}, but with the supplied
     *         assignables.
     */
    public AbstractUpdate changeAssignables(AbstractUpdate abstrUpd,
            Set<AbstrUpdateLHS> assignables) {
        final String phsID = abstrUpd.getAbstractPlaceholderStatement().getId();
        if (abstractUpdateInstances.get(phsID) == null) {
            abstractUpdateInstances.put(phsID, new LinkedHashMap<>());
        }

        final int assgnHashCode = assignables.hashCode();
        AbstractUpdate result = //
                abstractUpdateInstances.get(phsID).get(assgnHashCode);
        if (result == null) {
            result = abstrUpd.changeAssignables(assignables);
            abstractUpdateInstances.get(phsID).put(assgnHashCode, result);
        }

        return result;
    }

    /**
     * Returns a new {@link AbstractUpdate} of the supplied one with the
     * {@link ProgramVariable}s in the assignables replaced according to the
     * supplied map.
     *
     * @param replMap
     *            The replace map.
     * @return A new {@link AbstractUpdate} of this one with the
     *         {@link ProgramVariable}s in the assignables replaced according to
     *         the supplied map.
     */
    public AbstractUpdate changeAssignables(AbstractUpdate abstrUpd,
            Map<ProgramVariable, ProgramVariable> replMap) {
        final Set<AbstrUpdateLHS> newAssignables = abstrUpd.getAllAssignables()
                .stream().map(lhs -> lhs.replaceVariables(replMap))
                .map(AbstrUpdateLHS.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
        return changeAssignables(abstrUpd, newAssignables);
    }

    /**
     * Extracts all {@link AbstractUpdateLoc}s from the given union (set or
     * locset) {@link Term}.
     *
     * @param t
     *            The {@link Term} to extract all {@link AbstractUpdateLoc}s
     *            from.
     * @param ec
     *            The {@link ExecutionContext}, for handling fields.
     * @param services
     *            The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term}.
     */
    public static Set<AbstractUpdateLoc> abstractUpdateLocsFromUnionTerm(Term t,
            ExecutionContext ec, Services services) {
        return abstractUpdateLocsFromUnionTerm(t, Optional.of(ec), services);
    }

    /**
     * Extracts all {@link AbstractUpdateLoc}s from the given union (set or
     * locset) {@link Term}.
     *
     * @param t
     *            The {@link Term} to extract all {@link AbstractUpdateLoc}s
     *            from.
     * @param ec
     *            The {@link ExecutionContext}, for handling fields. If an empty
     *            {@link Optional} is supplied, fields are ignored.
     * @param services
     *            The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term}.
     */
    public static Set<AbstractUpdateLoc> abstractUpdateLocsFromUnionTerm(Term t,
            Optional<ExecutionContext> ec, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final ImmutableSet<Term> set;

        if (t.sort() == services.getTypeConverter().getLocSetLDT()
                .targetSort()) {
            set = tb.locsetUnionToSet(t);
        } else if (t.sort() == services.getTypeConverter().getSetLDT()
                .targetSort()) {
            set = tb.setUnionToImmutableSet(t);
        } else {
            assert false;
            return null;
        }

        return set.stream()
                .map(sub -> abstractUpdateLocFromTerm(sub, ec, services))
                .filter(loc -> !(loc instanceof EmptyLoc))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    /**
     * Extracts the {@link AbstractUpdateLoc} represented by the given
     * {@link Term}. May fail; in this case, an empty {@link Optional} is
     * returned.
     *
     * @param t
     *            The {@link Term} to extract all {@link AbstractUpdateLoc}s
     *            from.
     * @param ec
     *            The {@link ExecutionContext}, for handling fields.
     * @param services
     *            The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term}.
     */
    public Optional<AbstractUpdateLoc> tryExtractAbstrUpdateLocFromTerm(Term t,
            ExecutionContext ec, Services services) {
        return tryExtractAbstrUpdateLocFromTerm(t, Optional.of(ec), services);
    }

    /**
     * Extracts the {@link AbstractUpdateLoc} represented by the given
     * {@link Term}. May fail; in this case, an empty {@link Optional} is
     * returned. Make sure you don't rely on a result being present in
     * soundness-critical applications. It's safe to use this method, e.g., for
     * checking whether an update may be dropped, where in the empty case,
     * nothing happens (at most completeness issue).
     *
     * @param t
     *            The {@link Term} to extract all {@link AbstractUpdateLoc}s
     *            from.
     * @param ec
     *            The {@link ExecutionContext}, for handling fields. If an empty
     *            {@link Optional} is supplied, fields are ignored.
     * @param services
     *            The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term}.
     */
    public static Optional<AbstractUpdateLoc> tryExtractAbstrUpdateLocFromTerm(
            Term t, Optional<ExecutionContext> ec, Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        final TypeConverter tc = services.getTypeConverter();

        final Operator op = t.op();

        if (op instanceof LocationVariable) {
            return Optional.of(new PVLoc((LocationVariable) op));
        } else if (t.op() == locSetLDT.getAllLocs()) {
            return Optional.of(new AllLocsLoc(locSetLDT.getAllLocs()));
        } else if (t.op() == locSetLDT.getEmpty()) {
            return Optional.of(new EmptyLoc(locSetLDT.getEmpty()));
        } else if (op instanceof Function && op.arity() == 0
                && ((Function) op).sort() == locSetLDT.targetSort()) {
            return Optional.of(new SkolemLoc((Function) op));
        } else if (t.isRigid() && t.sort() != locSetLDT.targetSort()) {
            return Optional.of(new RigidRHS(t));
        } else if (op == locSetLDT.getSingletonPV()) {
            return Optional
                    .of(abstractUpdateLocFromTerm(t.sub(0), ec, services));
        } else if (op == locSetLDT.getHasTo()) {
            final AbstractUpdateLoc subResult = abstractUpdateLocFromTerm(
                    t.sub(0), ec, services);
            assert subResult instanceof AbstrUpdateLHS;
            return Optional.of(new HasToLoc((AbstrUpdateLHS) subResult));
        } else if (op == locSetLDT.getSingleton()) {
            if (!ec.isPresent()) {
                /*
                 * In this case, the caller is not interested in fields (or
                 * otherwise, should have supplied an ExecutionContext).
                 */
                return Optional.of(new EmptyLoc(locSetLDT.getEmpty()));
            }

            final Term obj = t.sub(0);
            final Term field = t.sub(1);
            final Term selectTerm = tb.select(
                    services.getJavaInfo().objectSort(), tb.getBaseHeap(), obj,
                    field);
            return Optional.of(
                    fieldLocFromSelectTerm(selectTerm, tc, ec.get(), services));
        } else if (heapLDT.isSelectOp(op) && t.subs().size() == 3
                && t.sub(2).op() == heapLDT.getArr()) {
            return Optional.of(new ArrayLoc(t.sub(1), t.sub(2).sub(0)));
        } else if (heapLDT.isSelectOp(op)) {
            if (!ec.isPresent()) {
                /*
                 * In this case, the caller is not interested in fields (or
                 * otherwise, should have supplied an ExecutionContext).
                 */
                return Optional.ofNullable(new EmptyLoc(locSetLDT.getEmpty()));
            }

            /*
             * NOTE (DS, 2019-03-06): This may fail (and we return an empty
             * optional), e.g. for strange select terms with update applications
             * inside.
             */
            return Optional.ofNullable(
                    fieldLocFromSelectTerm(t, tc, ec.get(), services));
        } else {
            return Optional.empty();
        }
    }

    /**
     * Extracts the {@link AbstractUpdateLoc} represented by the given
     * {@link Term}. Returns null in case of failure. Call
     * {@link #tryExtractAbstrUpdateLocFromTerm(Term, Optional, Services)} if
     * failure is expected.
     *
     * @param t
     *            The {@link Term} to extract all {@link AbstractUpdateLoc}s
     *            from.
     * @param ec
     *            The {@link ExecutionContext}, for handling fields. If an empty
     *            {@link Optional} is supplied, fields are ignored.
     * @param services
     *            The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term}.
     */
    public static AbstractUpdateLoc abstractUpdateLocFromTerm(Term t,
            Optional<ExecutionContext> ec, Services services) {
        Optional<AbstractUpdateLoc> result = tryExtractAbstrUpdateLocFromTerm(t,
                ec, services);
        if (!result.isPresent()) {
            assert false : "Unexpected element of loc set union.";
            return null;
        }
        return result.get();
    }

    /**
     * Extracts a {@link FieldLoc} from a select {@link Term}. Returns null if
     * this is not possible.
     *
     * @param selectTerm
     *            The select {@link Term}.
     * @param tc
     *            The {@link TypeConverter} for converting the select term to an
     *            program {@link Expression}.
     * @param ec
     *            The {@link ExecutionContext} for creating the field.
     * @param services
     *            The {@link Services} object.
     * @return A {@link FieldLoc} from the {@link Term}.
     */
    private static FieldLoc fieldLocFromSelectTerm(Term selectTerm,
            final TypeConverter tc, ExecutionContext ec, Services services) {
        final ReferencePrefix rtInst = ec.getRuntimeInstance();
        final TermBuilder tb = services.getTermBuilder();
        if (rtInst instanceof LocationVariable) {
            final LocationVariable rtInstVar = (LocationVariable) rtInst;
            selectTerm = GenericTermReplacer.replace(selectTerm,
                    t -> t.op() instanceof LocationVariable
                            && t.op().toString().equals("self")
                            && ((LocationVariable) t.op()).sort() == rtInstVar
                                    .sort(),
                    t -> tb.var((LocationVariable) rtInst), services);
        }

        /*
         * NOTE (DS, 2019-03-06): We currently don't distinguish different
         * heaps; either the abstract statement can or cannot assign a field,
         * this is independent of the used heap. Maybe we will have to
         * reconsider this, I might not have thought it through totally...
         */
        selectTerm = tb.select(selectTerm.sort(), tb.getBaseHeap(),
                selectTerm.sub(1), selectTerm.sub(2));

        final Expression pe;
        try {
            pe = tc.convertToProgramElement(selectTerm);
        } catch (Exception e) {
            return null;
        }

        if (pe instanceof FieldReference) {
            return new FieldLoc((FieldReference) pe, ec);
        } else if (pe instanceof ProgramVariable) {
            return new FieldLoc(new FieldReference((ProgramVariable) pe, null),
                    ec);
        } else {
            assert false : "Unexpected Expression type as result of field conversion";
            return null;
        }
    }

    /**
     * Transforms a set of abstract update right-hand sides to a set union term.
     *
     * @param accessibles
     *            The accessibles (right-hand sides) to construct the union term
     *            of.
     * @param services
     *            The services object.
     * @return A set union term from the given accessibles.
     */
    public Term accessiblesToSetUnion(Set<AbstrUpdateRHS> accessibles,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.setUnion(accessibles.stream().map(loc -> loc.toTerm(services))
                .map(tb::setSingleton).collect(Collectors.toList()));
    }
}
