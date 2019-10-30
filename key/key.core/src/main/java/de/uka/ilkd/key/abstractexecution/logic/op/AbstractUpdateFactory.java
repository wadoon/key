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

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.UniqueArrayList;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.EmptyLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.AllFieldsLocLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.ArrayLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.ArrayRange;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.FieldLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Factory class for {@link AbstractUpdate}s and {@link AbstractUpdate} LHSs /
 * RHSs.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractUpdateFactory {
    /**
     * Map from abstract program element (APE) identifiers to maps from hash codes
     * of assignables to abstract updates. Idea: Give me an APE name and the
     * left-hand side, I'll give you the {@link AbstractUpdate} operator if it has
     * been created already.
     */
    private final Map<String, Map<Integer, AbstractUpdate>> abstractUpdateInstances = new LinkedHashMap<>();

    /**
     * Map from abstract program element (APE) identifiers to function symbols for
     * corresponding abstract path conditions.
     */
    private final Map<String, Function> abstractPathConditionInstances = new LinkedHashMap<>();

    /**
     * Map from abstract update names to maps from place numbers in abstract updates
     * to functions representing the effect of the abstract update on the location
     * (has to be a program variable, other things don't make sense) at that place.
     */
    private final Map<String, Map<Integer, Function>> abstrUpdCharacteristicFuncInsts = new LinkedHashMap<>();

    private final Services services;

    /**
     * Constructor. NOTE: You should not use this constructor, but instead access
     * {@link Services#abstractUpdateFactory()}, since this factory caches
     * {@link AbstractUpdate}s. You'll probably face incompleteness issues if you
     * don't follow this rule.
     */
    public AbstractUpdateFactory(final Services services) {
        this.services = services;
    }

    /**
     * Returns abstract update operator for the passed
     * {@link AbstractPlaceholderStatement} and left-hand side.
     *
     * @param phs              The {@link AbstractPlaceholderStatement} for which
     *                         this {@link AbstractUpdate} should be created.
     * @param lhs              The update's left-hand side. Should be a
     *                         {@link SetLDT} term.
     * @param rhs              The right-hand side for the abstract update; needed
     *                         to extract the argument sorts for the operator.
     * @param executionContext An optional runtime instance {@link LocationVariable}
     *                         to normalize self terms (because otherwise, there
     *                         might be different such terms around).
     * @return The {@link AbstractUpdate} for the given
     *         {@link AbstractPlaceholderStatement} and left-hand side.
     */
    public AbstractUpdate getInstance(AbstractPlaceholderStatement phs, Term lhs, Term rhs,
            Optional<ExecutionContext> executionContext) {
        final UniqueArrayList<AbstractUpdateLoc> assignables = //
                abstrUpdateLocsFromTerm(lhs, executionContext, services).stream()
                        .map(AbstractUpdateLoc.class::cast)
                        .collect(Collectors.toCollection(() -> new UniqueArrayList<>()));

        final int numArgs = //
                (int) abstrUpdateLocsFromTerm(rhs, executionContext, services).stream().count();

        return getInstance(phs, assignables, numArgs);
    }

    /**
     * Returns abstract update operator for the passed
     * {@link AbstractPlaceholderStatement} and left-hand side.
     *
     * @param phs      The {@link AbstractPlaceholderStatement} for which this
     *                 {@link AbstractUpdate} should be created.
     * @param numArgs  The update's left-hand side.
     * @param argSorts The number of arguments of the abstract update.
     * @return The {@link AbstractUpdate} for the given
     *         {@link AbstractPlaceholderStatement} and left-hand side.
     */
    public AbstractUpdate getInstance(AbstractPlaceholderStatement phs,
            UniqueArrayList<AbstractUpdateLoc> assignables, final int numArgs) {
        final String phsID = phs.getId();
        if (abstractUpdateInstances.get(phsID) == null) {
            abstractUpdateInstances.put(phsID, new LinkedHashMap<>());
        }

        final int assgnHashCode = assignables.hashCode();
        AbstractUpdate result = //
                abstractUpdateInstances.get(phsID).get(assgnHashCode);
        if (result == null) {
            final Sort[] sorts = new Sort[numArgs];
            Arrays.fill(sorts, Sort.ANY);
            result = new AbstractUpdate(phs, assignables, sorts, services);
            abstractUpdateInstances.get(phsID).put(assgnHashCode, result);
        }

        return result;
    }

    /**
     * Returns the characteristic function for the position-th position in abstrUpd.
     * Assumes the assignable operator at that position in the update to be a
     * {@link PVLoc}, otherwise will fail.
     *
     * @param abstrUpd The {@link AbstractUpdate} for which to create the
     *                 characteristic function.
     * @param position The position for which to create the function.
     * @return The created (or cached) function.
     */
    public Function getCharacteristicFunctionForPosition(AbstractUpdate abstrUpd, int position) {
        final String abstractUpdName = abstrUpd.getUpdateName();
        if (abstrUpdCharacteristicFuncInsts.get(abstractUpdName) == null) {
            abstrUpdCharacteristicFuncInsts.put(abstractUpdName, new LinkedHashMap<>());
        }

        Function result = //
                abstrUpdCharacteristicFuncInsts.get(abstractUpdName).get(position);
        if (result == null) {
            final String funName = services.getTermBuilder()
                    .newName("f_" + abstractUpdName + "_" + position);

            final AbstractUpdateLoc relevantAssignable = //
                    abstrUpd.getAllAssignables().get(position);

            assert characteristicFunctionCreatedSupportedFor(relevantAssignable) : //
            "Characteristic abstract update functions not supported for type "
                    + relevantAssignable.getClass().getCanonicalName();

            result = new Function(new Name(funName), relevantAssignable.sort(), true, true,
                    abstrUpd.argSorts().toArray(new Sort[0]));

            abstrUpdCharacteristicFuncInsts.get(abstractUpdName).put(position, result);
        }

        return result;
    }

    /**
     * @param loc The {@link AbstractUpdateLoc} to check.
     * @return true iff we can create a characteristic function for the given
     *         location.
     */
    private static boolean characteristicFunctionCreatedSupportedFor(final AbstractUpdateLoc loc) {
        final AbstractUpdateLoc unwrappedLoc = AbstractExecutionUtils.unwrapHasTo(loc);
        return unwrappedLoc instanceof PVLoc || unwrappedLoc instanceof FieldLoc;
    }

    /**
     * Returns abstract path condition operator for the passed
     * {@link AbstractPlaceholderStatement} and argument sorts.
     *
     * @param phs      The {@link AbstractPlaceholderStatement} for which this
     *                 abstract path condition operator should be created.
     * @param argSorts argument sorts for the operator (corresponding to right-hand
     *                 side/accessibles)
     * @return The abstract path condition operator for the passed
     *         {@link AbstractPlaceholderStatement} and argument sorts.
     */
    public Function getAbstractPathConditionInstance(AbstractPlaceholderStatement phs,
            final Sort[] argSorts) {
        final String phsID = phs.getId();
        Function result = abstractPathConditionInstances.get(phsID);

        if (result == null) {
            final String funName = services.getTermBuilder().newName("C_" + phsID);
            result = new Function(new Name(funName), Sort.FORMULA, argSorts);

            abstractPathConditionInstances.put(phsID, result);
        }

        return result;
    }

    /**
     * Checks whether the given function symbol is an abstract path condition.
     * Abstract path conditions are those created via
     * {@link #getAbstractPathConditionInstance(AbstractPlaceholderStatement, Sort[])},
     * other symbols won't be recognized.
     * 
     * @param f The {@link Function} symbol to check.
     * @return true iff this function symbol is an abstract path condition.
     */
    public boolean isAbstractPathCondition(Function f) {
        return abstractPathConditionInstances.containsValue(f);
    }

    /**
     * Returns a new {@link AbstractUpdate} for the same
     * {@link AbstractPlaceholderStatement}, but with a different assignable set
     * defined by the supplied substitutions.
     *
     * @param abstrUpd   The original {@link AbstractUpdate}.
     * @param replaceMap The replacement map for assignable locations.
     * @return A new {@link AbstractUpdate} with the left-hand side changed
     *         according to replaceMap.
     */
    public AbstractUpdate changeAssignables(final AbstractUpdate abstrUpd,
            final Map<? extends AbstractUpdateLoc, ? extends AbstractUpdateLoc> replaceMap) {
        final String phsID = abstrUpd.getAbstractPlaceholderStatement().getId();
        if (abstractUpdateInstances.get(phsID) == null) {
            abstractUpdateInstances.put(phsID, new LinkedHashMap<>());
        }

        // Also replace locations if they're wrapped in hasTos
        final Map<AbstractUpdateLoc, AbstractUpdateLoc> augmentedReplaceMap = //
                new LinkedHashMap<>(replaceMap);
        replaceMap.entrySet().stream().forEach(entry -> {
            if (!(entry.getKey() instanceof HasToLoc)) {
                augmentedReplaceMap.put(new HasToLoc(entry.getKey()),
                        new HasToLoc(entry.getValue()));
            }
        });

        final UniqueArrayList<AbstractUpdateLoc> newAssignables = //
                abstrUpd.getAllAssignables().stream().map(
                        assgn -> Optional.ofNullable(augmentedReplaceMap.get(assgn)).orElse(assgn))
                        .collect(Collectors.toCollection(() -> new UniqueArrayList<>()));

        final int assgnHashCode = newAssignables.hashCode();
        AbstractUpdate result = //
                abstractUpdateInstances.get(phsID).get(assgnHashCode);
        if (result == null) {
            result = abstrUpd.changeAssignables(newAssignables);
            abstractUpdateInstances.get(phsID).put(assgnHashCode, result);
        }

        return result;
    }

    /**
     * Returns a new {@link AbstractUpdate} of the supplied one with the
     * {@link ProgramVariable}s in the assignables replaced according to the
     * supplied map.
     * 
     * @param replMap The replace map.
     *
     * @return A new {@link AbstractUpdate} of this one with the
     *         {@link ProgramVariable}s in the assignables replaced according to the
     *         supplied map.
     */
    public AbstractUpdate changeAssignablePVs(AbstractUpdate abstrUpd,
            Map<ProgramVariable, ProgramVariable> replMap) {
        final Map<AbstractUpdateLoc, AbstractUpdateLoc> locReplMap = //
                replMap.entrySet().stream()
                        .collect(Collectors.toMap(e -> new PVLoc((LocationVariable) e.getKey()),
                                e -> new PVLoc((LocationVariable) e.getValue())));

        return changeAssignables(abstrUpd, locReplMap);
    }

    /**
     * Converts the given {@link Term} to the {@link AbstractUpdateLoc}s it is
     * representing. Throws a {@link RuntimeException} if the given {@link Term} is
     * not directly representing any locations (i.e., is not a LocSet term).
     *
     * @param t                The {@link Term} to extract all
     *                         {@link AbstractUpdateLoc}s from.
     * @param executionContext An optional runtime instance {@link LocationVariable}
     *                         to normalize self terms (because otherwise, there
     *                         might be different such terms around).
     * @param services         The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term} or null if
     *         the {@link Term} does not represent {@link AbstractUpdateLoc}s.
     */
    public static Set<AbstractUpdateLoc> abstrUpdateLocsFromTerm(Term t,
            Optional<ExecutionContext> executionContext, Services services) {
        final Set<AbstractUpdateLoc> result = new LinkedHashSet<>();
        t = MiscTools.simplifyUpdatesInTerm(t, services);

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        final Operator op = t.op();

        if (op instanceof LocationVariable) {
            result.add(new PVLoc((LocationVariable) op));
        } else if (t.op() == locSetLDT.getAllLocs()) {
            result.add(new AllLocsLoc(locSetLDT.getAllLocs()));
        } else if (t.op() == locSetLDT.getEmpty()) {
            result.add(new EmptyLoc(locSetLDT.getEmpty()));
        } else if (AbstractExecutionUtils.isAbstractSkolemLocationSet(op, services)) {
            result.add(new SkolemLoc((Function) op));
        } else if (op == locSetLDT.getSingletonPV()) {
            final Set<AbstractUpdateLoc> subResult = abstrUpdateLocsFromTerm(t.sub(0),
                    executionContext, services);

            result.addAll(subResult);
        } else if (op == locSetLDT.getHasTo()) {
            // There is exactly one location inside a hasTo
            final AbstractUpdateLoc subResult = abstrUpdateLocsFromTerm(t.sub(0), executionContext,
                    services).iterator().next();
            result.add(new HasToLoc((AbstractUpdateLoc) subResult));
        } else if (op == locSetLDT.getUnion()) {
            final Set<AbstractUpdateLoc> subResult1 = //
                    abstrUpdateLocsFromTerm(t.sub(0), executionContext, services);
            final Set<AbstractUpdateLoc> subResult2 = //
                    abstrUpdateLocsFromTerm(t.sub(1), executionContext, services);

            result.addAll(subResult1);
            result.addAll(subResult2);
        } else if (isHeapOp(op, locSetLDT, heapLDT)) {
            final Set<AbstractUpdateLoc> subResult = //
                    abstrUpdateAssgnLocsFromHeapTerm(t, executionContext, services);

            result.addAll(subResult);
        } else {
            throw new RuntimeException(
                    String.format("Unsupported term %s, cannot extract locs", t));
        }

        return result;
    }

    /**
     * Transforms the given heap term (for which
     * {@link #isHeapOp(Operator, LocSetLDT, HeapLDT)} has to be true) to the
     * represented set of {@link AbstractUpdateLoc}s. The term has to be of the
     * right form, e.g., a select operation is not allowed, since it is only
     * suitable for the right-hand side of an abstract update (use
     * {@link #abstrUpdateLocsFromHeapTerm(Term, Optional, Services)} for this).
     * LocSet terms, for instance, are allowed.
     * 
     * Returns null if it {@link Term} operator is unexpected.
     *
     * @param t                The {@link Term} to transform.
     * @param executionContext The optional runtime instance for self variable
     *                         transformation.
     * @param services         The {@link Services} object.
     * @return The contained {@link AbstractUpdateLoc}s.
     */
    private static Set<AbstractUpdateLoc> abstrUpdateAssgnLocsFromHeapTerm(Term t,
            Optional<ExecutionContext> executionContext, Services services) {
        final Set<AbstractUpdateLoc> result = new LinkedHashSet<>();

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        final Operator op = t.op();

        if (op == locSetLDT.getSingleton() && t.sub(1).op() == heapLDT.getArr()) {
            result.add(new ArrayLoc(t.sub(0), t.sub(1).sub(0)));
        } else if (op == locSetLDT.getSingleton()) {
            final Term obj = normalizeSelfVar(t.sub(0), executionContext, services);
            final Term field = t.sub(1);
            result.add(new FieldLoc(obj, field, services));
        } else if (t.op() == locSetLDT.getAllFields() && t.subs().size() == 1) {
            result.add(new AllFieldsLocLHS(t.sub(0)));
        } else if (t.op() == locSetLDT.getArrayRange()) {
            result.add(new ArrayRange(t.sub(0), t.sub(1), t.sub(2)));
        } else {
            return null;
        }

        return result;
    }

    private static boolean isHeapOp(final Operator op, final LocSetLDT locSetLDT,
            final HeapLDT heapLDT) {
        return op == locSetLDT.getArrayRange() || op == locSetLDT.getSingleton()
                || op == locSetLDT.getAllFields();
    }

    /**
     * If the operator of the given {@link Term} is a "self" variable, we normalize
     * it to the given executionContext if the {@link KeYJavaType}s of the variable
     * and the instance are the same.
     *
     * @param objTerm          The objTerm to normalize.
     * @param executionContext An optional runtime instance {@link LocationVariable}
     *                         to normalize self terms (because otherwise, there
     *                         might be different such terms around). For an empty
     *                         optional, we return objTerm.
     * @param services         The {@link Services} object (for the
     *                         {@link TermBuilder}).
     * @return The original objTemr if executionContext if empty, the objTerm is not
     *         a "self" term, or the types of the objTerm and the executionContext
     *         are different, or otherwise a {@link Term} with the runtime instance.
     */
    private static Term normalizeSelfVar(Term objTerm, Optional<ExecutionContext> executionContext,
            Services services) {
        // objTerm = MiscTools.simplifyUpdateApplication(objTerm, services);

        if (!executionContext.isPresent() || !(objTerm.op() instanceof LocationVariable)
                || !objTerm.op().toString().equals("self")
                || !((LocationVariable) objTerm.op()).sort().equals(
                        executionContext.get().getMethodContext().getContainerType().getSort())) {
            return objTerm;
        }

        return services.getTypeConverter().findThisForSort(
                executionContext.get().getMethodContext().getContainerType().getSort(),
                executionContext.get());
    }

    // TODO (DS, 2019-10-30): Leaving this code here for now in case that I need it.
    // Delete soon if that's not the case!
    //@formatter:off
//    /**
//     * Returns, for a term representing a field, the "canonical" field program
//     * variable.
//     *
//     * @param field    The field term, something like "my.package.Type::$field", of
//     *                 Sort "Field" (of {@link HeapLDT}).
//     * @param services The {@link Services} object (for {@link JavaInfo} and
//     *                 {@link HeapLDT}).
//     * @return The canonical program variable representing the field.
//     */
//    private static LocationVariable fieldPVFromFieldFunc(Term field, Services services) {
//        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
//        final JavaInfo javaInfo = services.getJavaInfo();
//        assert field.sort() == heapLDT.getFieldSort();
//
//        /*
//         * NOTE (DS, 2019-03-12): It sometimes happens that we get passed an update
//         * application here. In this case, the target is the field.
//         */
//        if (field.op() == UpdateApplication.UPDATE_APPLICATION) {
//            field = UpdateApplication.getTarget(field);
//            assert field.sort() == heapLDT.getFieldSort();
//        }
//
//        int sepIdx = field.toString().indexOf("::$");
//        int sepSize = 3;
//        if (sepIdx < 0) {
//            sepIdx = field.toString().indexOf("::<");
//            sepSize = 2;
//        }
//
//        assert sepIdx > 0;
//
//        final String typeStr = field.toString().substring(0, sepIdx);
//        final String fieldStr = field.toString().substring(sepIdx + sepSize);
//
//        final KeYJavaType kjt = javaInfo.getKeYJavaType(typeStr);
//        return (LocationVariable) javaInfo.getCanonicalFieldProgramVariable(fieldStr, kjt);
//    }
    //@formatter:on
}
