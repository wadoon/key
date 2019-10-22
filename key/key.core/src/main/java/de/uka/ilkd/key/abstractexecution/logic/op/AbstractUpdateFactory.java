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

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.EmptyLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.RigidRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.AllFieldsLocLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.AllFieldsLocRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.ArrayLocLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.ArrayLocRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.ArrayRange;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.FieldLocLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.FieldLocRHS;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.MiscTools;

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
     * Constructor. NOTE: You should not use this constructor, but instead access
     * {@link Services#abstractUpdateFactory()}, since this factory caches
     * {@link AbstractUpdate}s. You'll probably face incompleteness issues if you
     * don't follow this rule.
     */
    public AbstractUpdateFactory() {
    }

    /**
     * Returns abstract update operator for the passed
     * {@link AbstractPlaceholderStatement} and left-hand side.
     *
     * @param phs             The {@link AbstractPlaceholderStatement} for which
     *                        this {@link AbstractUpdate} should be created.
     * @param lhs             The update's left-hand side. Should be a
     *                        {@link SetLDT} term.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around).
     * @param services        The {@link Services} object.
     * @return The {@link AbstractUpdate} for the given
     *         {@link AbstractPlaceholderStatement} and left-hand side.
     */
    public AbstractUpdate getInstance(AbstractPlaceholderStatement phs, Term lhs,
            Optional<LocationVariable> runtimeInstance, Services services) {
        final LinkedHashSet<AbstractUpdateAssgnLoc> assignables = //
                abstrUpdateAssgnLocsFromTermSafe(lhs, runtimeInstance, services).stream()
                        .map(AbstractUpdateAssgnLoc.class::cast)
                        .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        return getInstance(phs, assignables, services);
    }

    /**
     * Returns abstract update operator for the passed
     * {@link AbstractPlaceholderStatement} and left-hand side.
     *
     * @param phs         The {@link AbstractPlaceholderStatement} for which this
     *                    {@link AbstractUpdate} should be created.
     * @param assignables The update's left-hand side.
     * @param services    The {@link Services} object.
     * @return The {@link AbstractUpdate} for the given
     *         {@link AbstractPlaceholderStatement} and left-hand side.
     */
    public AbstractUpdate getInstance(AbstractPlaceholderStatement phs,
            Set<AbstractUpdateAssgnLoc> assignables, Services services) {
        final String phsID = phs.getId();
        if (abstractUpdateInstances.get(phsID) == null) {
            abstractUpdateInstances.put(phsID, new LinkedHashMap<>());
        }

        final int assgnHashCode = assignables.hashCode();
        AbstractUpdate result = //
                abstractUpdateInstances.get(phsID).get(assgnHashCode);
        if (result == null) {
            result = new AbstractUpdate(phs, assignables, services);
            abstractUpdateInstances.get(phsID).put(assgnHashCode, result);
        }

        return result;
    }

    /**
     * Returns a new abstract update for the same
     * {@link AbstractPlaceholderStatement}, but with the supplied assignables.
     *
     * @param abstrUpd       The original {@link AbstractUpdate}.
     * @param newAssignables The new assignables (left-hand sides).
     * @return A new {@link AbstractUpdate} for the same
     *         {@link AbstractPlaceholderStatement}, but with the supplied
     *         assignables.
     */
    public AbstractUpdate changeAssignables(AbstractUpdate abstrUpd,
            Set<AbstractUpdateAssgnLoc> assignables) {
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
     * @param replMap  The replace map.
     * @param services The {@link Services} object.
     *
     * @return A new {@link AbstractUpdate} of this one with the
     *         {@link ProgramVariable}s in the assignables replaced according to the
     *         supplied map.
     */
    public AbstractUpdate changeAssignables(AbstractUpdate abstrUpd,
            Map<ProgramVariable, ProgramVariable> replMap, Services services) {
        final Set<AbstractUpdateAssgnLoc> newAssignables = abstrUpd.getAllAssignables().stream()
                .map(lhs -> lhs.replaceVariables(replMap, services))
                .map(AbstractUpdateAssgnLoc.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
        return changeAssignables(abstrUpd, newAssignables);
    }

    /**
     * Extracts from the given {@link Term} to the {@link AbstractUpdateLoc}s
     * contained in it.
     *
     * @param t               The {@link Term} to extract all
     *                        {@link AbstractUpdateLoc}s from.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around).
     * @param services        The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s in the given {@link Term}.
     */
    public static Set<AbstractUpdateLoc> extractAbstrUpdateLocsFromTerm(Term t,
            Optional<LocationVariable> runtimeInstance, Services services) {
        final Set<AbstractUpdateLoc> subResult = //
                abstrUpdateLocsFromTermUnsafe(t, runtimeInstance, services);
        if (subResult != null) {
            // We've found an atom
            return subResult;
        }

        final Set<AbstractUpdateLoc> result = new LinkedHashSet<>();
        for (Term sub : t.subs()) {
            result.addAll(Optional
                    .ofNullable(extractAbstrUpdateLocsFromTerm(sub, runtimeInstance, services))
                    .orElse(Collections.emptySet()));
        }
        return result;
    }

    /**
     * Converts the given {@link Term} to the {@link AbstractUpdateAssgnLoc}s it is
     * representing. Throws a {@link RuntimeException} if the given {@link Term} is
     * not directly representing any locations; use
     * {@link #extractAbstrUpdateAssgnLocsFromTerm(Term, Optional, Services)} for
     * extraction if the passed {@link Term} does not have to represent locations.
     *
     * @param t               The {@link Term} to extract all
     *                        {@link AbstractUpdateLoc}s from.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around).
     * @param services        The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term} or null if
     *         the {@link Term} does not represent {@link AbstractUpdateLoc}s.
     */
    public static Set<AbstractUpdateAssgnLoc> abstrUpdateAssgnLocsFromTermSafe(Term t,
            Optional<LocationVariable> runtimeInstance, Services services) {
        return Optional.ofNullable( //
                abstrUpdateAssgnLocsFromTermUnsafe(t, runtimeInstance, services))
                .orElseThrow(() -> new RuntimeException(
                        String.format("Unsupported term %s, cannot extract locs", t)));
    }

    /**
     * Converts the given {@link Term} to the {@link AbstractUpdateLoc}s it is
     * representing. Throws a {@link RuntimeException} if the given {@link Term} is
     * not directly representing any locations; use
     * {@link #extractAbstrUpdateLocsFromTerm(Term, Optional, Services)} for
     * extraction if the passed {@link Term} does not have to represent locations.
     *
     * @param t               The {@link Term} to extract all
     *                        {@link AbstractUpdateLoc}s from.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around).
     * @param services        The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term} or null if
     *         the {@link Term} does not represent {@link AbstractUpdateLoc}s.
     */
    public static Set<AbstractUpdateLoc> abstrUpdateLocsFromTermSafe(Term t,
            Optional<LocationVariable> runtimeInstance, Services services) {
        return Optional.ofNullable(abstrUpdateLocsFromTermUnsafe(t, runtimeInstance, services))
                .orElseThrow(() -> new RuntimeException(
                        String.format("Unsupported term %s, cannot extract locs", t)));
    }

    /**
     * Converts the given {@link Term} to the {@link AbstractUpdateAssgnLoc}s it is
     * representing. Returns null if the given {@link Term} is not directly
     * representing any locations; use
     * {@link #extractAbstrUpdateAssgnLocsFromTerm(Term, Optional, Services)} for
     * extraction if the passed {@link Term} does not have to represent locations,
     * or {@link #abstrUpdateLocsAssgnFromTermSafe(Term, Optional, Services)} for a
     * variant ensuring that the result is non-null by throwing an exception (fail
     * early).
     *
     * @param t               The {@link Term} to extract all
     *                        {@link AbstractUpdateLoc}s from.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around).
     * @param services        The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term} or null if
     *         the {@link Term} does not represent {@link AbstractUpdateLoc}s.
     */
    public static Set<AbstractUpdateAssgnLoc> abstrUpdateAssgnLocsFromTermUnsafe(Term t,
            Optional<LocationVariable> runtimeInstance, Services services) {
        final Set<AbstractUpdateAssgnLoc> result = new LinkedHashSet<>();
        t = MiscTools.simplifyUpdatesInTerm(t, services);

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final SetLDT setLDT = services.getTypeConverter().getSetLDT();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        final Operator op = t.op();

        if (op instanceof LocationVariable) {
            result.add(new PVLoc((LocationVariable) op));
        } else if (t.op() == locSetLDT.getAllLocs()) {
            result.add(new AllLocsLoc(locSetLDT.getAllLocs()));
        } else if (t.op() == locSetLDT.getEmpty()) {
            result.add(new EmptyLoc(locSetLDT.getEmpty()));
        } else if (op instanceof Function && op.arity() == 0
                && ((Function) op).sort() == locSetLDT.targetSort()) {
            result.add(new SkolemLoc((Function) op));
        } else if (op == locSetLDT.getSingletonPV()) {
            final Set<AbstractUpdateAssgnLoc> subResult = abstrUpdateAssgnLocsFromTermUnsafe(
                    t.sub(0), runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            result.addAll(subResult);
        } else if (op == locSetLDT.getHasTo()) {
            // There is exactly one location inside a hasTo
            final AbstractUpdateAssgnLoc subResult = abstrUpdateAssgnLocsFromTermUnsafe(t.sub(0),
                    runtimeInstance, services).iterator().next();
            if (subResult == null) {
                return null;
            }

            assert subResult instanceof AbstractUpdateAssgnLoc;
            result.add(new HasToLoc((AbstractUpdateAssgnLoc) subResult));
        } else if (op == locSetLDT.getUnion() || op == setLDT.getUnion()) {
            final Set<AbstractUpdateAssgnLoc> subResult1 = abstrUpdateAssgnLocsFromTermUnsafe(
                    t.sub(0), runtimeInstance, services);
            final Set<AbstractUpdateAssgnLoc> subResult2 = abstrUpdateAssgnLocsFromTermUnsafe(
                    t.sub(1), runtimeInstance, services);
            if (subResult1 == null || subResult2 == null) {
                return null;
            }

            result.addAll(subResult1);
            result.addAll(subResult2);
        } else if (op == setLDT.getSingleton()) {
            final Set<AbstractUpdateAssgnLoc> subResult = abstrUpdateAssgnLocsFromTermUnsafe(
                    t.sub(0), runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            result.addAll(subResult);
        } else if (isLHSHeapOp(op, locSetLDT, heapLDT)) {
            final Set<AbstractUpdateAssgnLoc> subResult = //
                    abstrUpdateAssgnLocsFromHeapTerm(t, runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            result.addAll(subResult);
        } else {
            return null;
        }

        return result;
    }

    /**
     * Converts the given {@link Term} to the {@link AbstractUpdateLoc}s it is
     * representing. Returns null if the given {@link Term} is not directly
     * representing any locations; use
     * {@link #extractAbstrUpdateLocsFromTerm(Term, Optional, Services)} for
     * extraction if the passed {@link Term} does not have to represent locations,
     * or {@link #abstrUpdateLocsFromTermSafe(Term, Optional, Services)} for a
     * variant ensuring that the result is non-null by throwing an exception (fail
     * early).
     *
     * @param t               The {@link Term} to extract all
     *                        {@link AbstractUpdateLoc}s from.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around).
     * @param services        The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term} or null if
     *         the {@link Term} does not represent {@link AbstractUpdateLoc}s.
     */
    public static Set<AbstractUpdateLoc> abstrUpdateLocsFromTermUnsafe(Term t,
            Optional<LocationVariable> runtimeInstance, Services services) {
        final Set<AbstractUpdateLoc> result = new LinkedHashSet<>();
        t = MiscTools.simplifyUpdatesInTerm(t, services);

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final SetLDT setLDT = services.getTypeConverter().getSetLDT();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        final Operator op = t.op();

        if (op instanceof LocationVariable) {
            result.add(new PVLoc((LocationVariable) op));
        } else if (op == locSetLDT.getAllLocs()) {
            result.add(new AllLocsLoc(locSetLDT.getAllLocs()));
        } else if (op == locSetLDT.getEmpty()) {
            result.add(new EmptyLoc(locSetLDT.getEmpty()));
        } else if (op instanceof Function && op.arity() == 0
                && ((Function) op).sort() == locSetLDT.targetSort()) {
            result.add(new SkolemLoc((Function) op));
        } else if (op == locSetLDT.getSingletonPV()) {
            final Set<AbstractUpdateLoc> subResult = abstrUpdateLocsFromTermUnsafe(t.sub(0),
                    runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            result.addAll(subResult);
        } else if (op == locSetLDT.getUnion() || op == setLDT.getUnion()) {
            final Set<AbstractUpdateLoc> subResult1 = abstrUpdateLocsFromTermUnsafe(t.sub(0),
                    runtimeInstance, services);
            final Set<AbstractUpdateLoc> subResult2 = abstrUpdateLocsFromTermUnsafe(t.sub(1),
                    runtimeInstance, services);
            if (subResult1 == null || subResult2 == null) {
                return null;
            }

            result.addAll(subResult1);
            result.addAll(subResult2);
        } else if (op == setLDT.getSingleton()) {
            final Set<AbstractUpdateLoc> subResult = abstrUpdateLocsFromTermUnsafe(t.sub(0),
                    runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            result.addAll(subResult);
        } else if (isRHSHeapOp(op, locSetLDT, heapLDT)) {
            final Set<AbstractUpdateLoc> subResult = //
                    abstrUpdateLocsFromHeapTerm(t, runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            result.addAll(subResult);
        } else if (t.isRigid() && t.sort() != locSetLDT.targetSort()
                && t.sort() != heapLDT.getFieldSort()) {
            result.add(new RigidRHS(t));
        } else if (op == IfThenElse.IF_THEN_ELSE) {
            for (int i = 1; i <= 2; i++) {
                final Set<AbstractUpdateLoc> subResult = abstrUpdateLocsFromTermUnsafe(t.sub(i),
                        runtimeInstance, services);
                if (subResult == null) {
                    return null;
                }

                result.addAll(subResult);
            }
        } else {
            return null;
        }

        return result;
    }

    /**
     * Transforms the given heap term (for which
     * {@link #isLHSHeapOp(Operator, LocSetLDT, HeapLDT)} has to be true) to the
     * represented set of {@link AbstractUpdateAssgnLoc}s. The term has to be of the
     * right form, e.g., a select operation is not allowed, since it is only
     * suitable for the right-hand side of an abstract update (use
     * {@link #abstrUpdateLocsFromHeapTerm(Term, Optional, Services)} for this).
     * LocSet terms, for instance, are allowed.
     * 
     * Returns null if it {@link Term} operator is unexpected.
     *
     * @param t               The {@link Term} to transform.
     * @param runtimeInstance The optional runtime instance for self variable
     *                        transformation.
     * @param services        The {@link Services} object.
     * @return The contained {@link AbstractUpdateLoc}s.
     */
    private static Set<AbstractUpdateAssgnLoc> abstrUpdateAssgnLocsFromHeapTerm(Term t,
            Optional<LocationVariable> runtimeInstance, Services services) {
        final Set<AbstractUpdateAssgnLoc> result = new LinkedHashSet<>();

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        final Operator op = t.op();

        if (op == locSetLDT.getSingleton() && t.sub(1).op() == heapLDT.getArr()) {
            result.add(new ArrayLocLHS(t.sub(0), t.sub(1).sub(0)));
        } else if (op == locSetLDT.getSingleton()) {
            final Term obj = //
                    normalizeSelfVar(t.sub(0), runtimeInstance, services);
            final Term field = t.sub(1);
            // XXX (DS. 2019-10-22): It's problematic to convert the field to a PV here; we
            // can, for instance, pass the location (o,f) for some symbols o, f created out
            // of the blue inside a KeY file, then there's no name inside the f that we
            // could extract and that call will fail.
            result.add(new FieldLocLHS(obj, fieldPVFromFieldFunc(field, services)));
        } else if (t.op() == locSetLDT.getAllFields() && t.subs().size() == 1) {
            result.add(new AllFieldsLocLHS(t.sub(0)));
        } else if (t.op() == locSetLDT.getArrayRange()) {
            result.add(new ArrayRange(t.sub(0), t.sub(1), t.sub(2)));
        } else {
            return null;
        }

        return result;
    }

    /**
     * Transforms the given heap term (for which
     * {@link #isRHSHeapOp(Operator, LocSetLDT, HeapLDT)} has to be true) to the
     * represented set of {@link AbstractUpdateLoc}s. Returns null if it
     * {@link Term} operator is unexpected.
     *
     * @param t               The {@link Term} to transform.
     * @param runtimeInstance The optional runtime instance for self variable
     *                        transformation.
     * @param services        The {@link Services} object.
     * @return The contained {@link AbstractUpdateLoc}s.
     */
    private static Set<AbstractUpdateLoc> abstrUpdateLocsFromHeapTerm(Term t,
            Optional<LocationVariable> runtimeInstance, Services services) {
        final Set<AbstractUpdateLoc> result = new LinkedHashSet<>();

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        final Term tWoUpd = stripUpd(t);
        @SuppressWarnings("unchecked")
        final Optional<Term>[] subs = new Optional[3];
        for (int i = 0; i <= 2; i++) {
            subs[i] = tWoUpd.subs().size() > i ? //
                    Optional.of(stripUpd(tWoUpd.sub(i))) : //
                    Optional.empty();
        }

        final Operator op = tWoUpd.op();

        if (op instanceof LocationVariable) {
            /* This is the heap LV, in which we are not interested here. */
            /*
             * TODO (DS, 2019-05-27): Seems that we still need it, check if that breaks
             * anything.
             */
            result.add(new PVLoc((LocationVariable) op));
        } else if (op == locSetLDT.getSingleton() && subs[1].get().op() == heapLDT.getArr()) {
            result.add(new ArrayLocRHS(subs[0].get(), subs[1].get().sub(0)));
        } else if (op == locSetLDT.getSingleton()) {
            final Term obj = //
                    normalizeSelfVar(subs[0].get(), runtimeInstance, services);
            final Term field = subs[1].get();
            result.add(new FieldLocRHS(Optional.empty(), Optional.empty(), obj,
                    fieldPVFromFieldFunc(field, services)));
        } else if (tWoUpd.op() == locSetLDT.getAllFields() && tWoUpd.subs().size() == 1) {
            result.add(new AllFieldsLocRHS(subs[0].get()));
        } else if (tWoUpd.op() == locSetLDT.getArrayRange()) {
            result.add(new ArrayRange(subs[0].get(), subs[1].get(), subs[2].get()));
        } else if (heapLDT.isSelectOp(op) && tWoUpd.subs().size() == 3
                && subs[2].get().op() == heapLDT.getArr()) {
            final Term heapTerm = subs[0].get();
            final Term obj = //
                    normalizeSelfVar(subs[1].get(), runtimeInstance, services);
            final Term array = subs[2].get().sub(0);
            result.add(new ArrayLocRHS(obj, array));

            final Set<AbstractUpdateLoc> subResult = abstrUpdateLocsFromHeapTerm(heapTerm,
                    runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            result.addAll(subResult);
        } else if (heapLDT.isSelectOp(op)) {
            final Sort sort = heapLDT.getSortOfSelect(op);
            final Term heapTerm = subs[0].get();
            final Term field = subs[2].get();

            /*
             * If the field is a logic variable, it's part of the assignable clause or
             * something that we're not interested in, since it has to be in the scope of a
             * quantifier.
             */
            if (!(field.op() instanceof LogicVariable)) {
                final Term obj = normalizeSelfVar(tWoUpd.sub(1), runtimeInstance, services);
                result.add(new FieldLocRHS(Optional.of(sort), Optional.of(heapTerm), obj,
                        fieldPVFromFieldFunc(field, services)));

                final Set<AbstractUpdateLoc> subResult = abstrUpdateLocsFromHeapTerm(heapTerm,
                        runtimeInstance, services);
                if (subResult != null) {
                    result.addAll(subResult);
                }
            }
        } else if (op == heapLDT.getStore() && tWoUpd.subs().size() == 4
                && subs[2].get().op() == heapLDT.getArr()) {
            /*
             * TODO (DS, 2019-05-22): Check what happens if the array is not a local
             * variable, but a field...
             */

            final Term heapTerm = tWoUpd.sub(0);
            final Term array = normalizeSelfVar(subs[1].get(), runtimeInstance, services);
            final Term index = subs[2].get();
            result.add(new ArrayLocRHS(array, index.sub(0)));

            final Set<AbstractUpdateLoc> subResult = //
                    abstrUpdateLocsFromHeapTerm(heapTerm, runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            result.addAll(subResult);
        } else if (op == heapLDT.getStore()) {
            final Term heapTerm = subs[0].get();
            final Term obj = normalizeSelfVar(subs[1].get(), runtimeInstance, services);
            final Term field = subs[2].get();
            result.add(new FieldLocRHS(Optional.empty(), Optional.empty(), obj,
                    fieldPVFromFieldFunc(field, services)));

            final Set<AbstractUpdateLoc> subResult = abstrUpdateLocsFromHeapTerm(heapTerm,
                    runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            result.addAll(subResult);
        } else if (op == heapLDT.getAnon()) {
            /*
             * TODO (DS, 2019-05-23): Check that the right thing is done here, I'm not
             * completely sure. Since this method is only about right-hand sides, nothing is
             * assigned...
             */
            final Term heapTerm = subs[0].get();
            final Term anonLocsTerm = subs[1].get();

            Set<AbstractUpdateLoc> subResult = abstrUpdateLocsFromTermUnsafe(anonLocsTerm,
                    runtimeInstance, services);
            if (subResult == null) {
                return null;
            }

            if (subResult.stream().anyMatch(loc -> loc instanceof AllLocsLoc)) {
                /*
                 * All of this heap is anonymized -> return the elements of the heap, since all
                 * those are assigned.
                 */
                subResult = abstrUpdateLocsFromTermUnsafe(heapTerm, runtimeInstance, services);
                if (subResult == null) {
                    return null;
                }
            }

            result.addAll(subResult);
        } else {
            return null;
        }

        return result;
    }

    private static Term stripUpd(Term t) {
        return TermBuilder.goBelowUpdates(t);
    }

    private static boolean isLHSHeapOp(final Operator op, final LocSetLDT locSetLDT,
            final HeapLDT heapLDT) {
        return op == locSetLDT.getArrayRange() || op == locSetLDT.getSingleton()
                || op == locSetLDT.getAllFields();
    }

    private static boolean isRHSHeapOp(final Operator op, final LocSetLDT locSetLDT,
            final HeapLDT heapLDT) {
        return op == locSetLDT.getArrayRange() || op == locSetLDT.getSingleton()
                || heapLDT.isSelectOp(op) || op == heapLDT.getStore() || op == heapLDT.getAnon()
                || op == locSetLDT.getAllFields();
    }

    /**
     * If the operator of the given {@link Term} is a "self" variable, we normalize
     * it to the given runtimeInstance if the {@link KeYJavaType}s of the variable
     * and the instance are the same.
     *
     * @param objTerm         The objTerm to normalize.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around). For an empty
     *                        optional, we return objTerm.
     * @param services        The {@link Services} object (for the
     *                        {@link TermBuilder}).
     * @return The original objTemr if runtimeInstance if empty, the objTerm is not
     *         a "self" term, or the types of the objTerm and the runtimeInstance
     *         are different, or otherwise a {@link Term} with the runtime instance.
     */
    private static Term normalizeSelfVar(Term objTerm, Optional<LocationVariable> runtimeInstance,
            Services services) {
        // objTerm = MiscTools.simplifyUpdateApplication(objTerm, services);

        if (!runtimeInstance.isPresent() || !(objTerm.op() instanceof LocationVariable)
                || !objTerm.op().toString().equals("self")
                || !((LocationVariable) objTerm.op()).sort().equals(runtimeInstance.get().sort())) {
            return objTerm;
        }

        return services.getTermBuilder().var(runtimeInstance.get());
    }

    /**
     * Returns, for a term representing a field, the "canonical" field program
     * variable.
     *
     * @param field    The field term, something like "my.package.Type::$field", of
     *                 Sort "Field" (of {@link HeapLDT}).
     * @param services The {@link Services} object (for {@link JavaInfo} and
     *                 {@link HeapLDT}).
     * @return The canonical program variable representing the field.
     */
    private static LocationVariable fieldPVFromFieldFunc(Term field, Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final JavaInfo javaInfo = services.getJavaInfo();
        assert field.sort() == heapLDT.getFieldSort();

        /*
         * NOTE (DS, 2019-03-12): It sometimes happens that we get passed an update
         * application here. In this case, the target is the field.
         */
        if (field.op() == UpdateApplication.UPDATE_APPLICATION) {
            field = UpdateApplication.getTarget(field);
            assert field.sort() == heapLDT.getFieldSort();
        }

        int sepIdx = field.toString().indexOf("::$");
        int sepSize = 3;
        if (sepIdx < 0) {
            sepIdx = field.toString().indexOf("::<");
            sepSize = 2;
        }

        assert sepIdx > 0;

        final String typeStr = field.toString().substring(0, sepIdx);
        final String fieldStr = field.toString().substring(sepIdx + sepSize);

        final KeYJavaType kjt = javaInfo.getKeYJavaType(typeStr);
        return (LocationVariable) javaInfo.getCanonicalFieldProgramVariable(fieldStr, kjt);
    }

    /**
     * Transforms a set of abstract update right-hand sides to a set union term.
     *
     * @param accessibles The accessibles (right-hand sides) to construct the union
     *                    term of.
     *
     * @param services    The services object.
     *
     * @return A set union term from the given accessibles.
     */
    public Term accessiblesToSetUnion(Set<AbstractUpdateLoc> accessibles, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.setUnion(accessibles.stream().map(loc -> loc.toTerm(services))
                .map(tb::setSingleton).collect(Collectors.toList()));
    }

    /**
     * Extracts a set of {@link AbstrUpdateUpdatableLoc}s from a set union which is
     * the right-hand side of an {@link AbstractUpdate} {@link Term}. Returns null
     * if there is an unexpected operator in the term (might happen for intermediate
     * stages in heap simplification, etc.).
     *
     * @param t               The right-hand side to transform.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around).
     * @param services        The {@link Services} object.
     * @return The {@link Set} of {@link AbstrUpdateUpdatableLoc}s represented by t.
     */
    public static Set<AbstractUpdateLoc> getUpdatableRHSsUnsafe(Term t,
            Optional<LocationVariable> runtimeInstance, Services services) {
        // XXX This makes no sense any more.
        final Set<AbstractUpdateLoc> locs = //
                abstrUpdateLocsFromTermUnsafe(t, runtimeInstance, services);
        if (locs == null) {
            return null;
        }

        return locs.stream().filter(AbstractUpdateLoc.class::isInstance)
                .map(AbstractUpdateLoc.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    /**
     * Extracts a set of {@link AbstrUpdateUpdatableLoc}s from a set union which is
     * the right-hand side of an {@link AbstractUpdate} {@link Term}.
     *
     * @param t               The right-hand side to transform.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around).
     * @param services        The {@link Services} object.
     * @return The {@link Set} of {@link AbstrUpdateUpdatableLoc}s represented by t.
     */
    public static Set<AbstractUpdateLoc> getUpdatableRHSsSafe(Term t,
            Optional<LocationVariable> runtimeInstance, Services services) {
        // XXX This makes no sense any more.
        return abstrUpdateLocsFromTermSafe(t, runtimeInstance, services).stream()
                .filter(AbstractUpdateLoc.class::isInstance).map(AbstractUpdateLoc.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }
}
