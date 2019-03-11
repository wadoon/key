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

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.DefaultImmutableSet;
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
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

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
                abstractUpdateLocsFromUnionTerm(lhs, services).stream()
                        .map(AbstrUpdateLHS.class::cast).collect(Collectors
                                .toCollection(() -> new LinkedHashSet<>()));

        return getInstance(phs, assignables, services);
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
     * @param services
     *            The {@link Services} object.
     * @return The {@link AbstractUpdate} for the given
     *         {@link AbstractPlaceholderStatement} and left-hand side.
     */
    public AbstractUpdate getInstance(AbstractPlaceholderStatement phs,
            Set<AbstrUpdateLHS> assignables, Services services) {
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
     * @param services
     *            The {@link Services} object.
     *
     * @return A new {@link AbstractUpdate} of this one with the
     *         {@link ProgramVariable}s in the assignables replaced according to
     *         the supplied map.
     */
    public AbstractUpdate changeAssignables(AbstractUpdate abstrUpd,
            Map<ProgramVariable, ProgramVariable> replMap, Services services) {
        final Set<AbstrUpdateLHS> newAssignables = abstrUpd.getAllAssignables()
                .stream().map(lhs -> lhs.replaceVariables(replMap, services))
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
     * @param services
     *            The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term}.
     */
    public static Set<AbstractUpdateLoc> abstractUpdateLocsFromUnionTerm(Term t,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final ImmutableSet<Term> set;

        if (t.sort() == services.getTypeConverter().getLocSetLDT()
                .targetSort()) {
            set = tb.locsetUnionToSet(t);
        } else if (t.sort() == services.getTypeConverter().getSetLDT()
                .targetSort()) {
            set = tb.setUnionToImmutableSet(t);
        } else {
            set = DefaultImmutableSet.<Term> nil().add(t);
        }

        return set.stream().map(sub -> abstrUpdateLocsFromTerm(sub, services))
                .flatMap(Collection::stream)
                .filter(loc -> !(loc instanceof EmptyLoc))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    /**
     * Extracts from the given {@link Term} to the {@link AbstractUpdateLoc}s
     * contained in it.
     *
     * @param t
     *            The {@link Term} to extract all {@link AbstractUpdateLoc}s
     *            from.
     * @param services
     *            The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s in the given {@link Term}.
     */
    public static Set<AbstractUpdateLoc> extractAbstrUpdateLocsFromTerm(Term t,
            Services services) {
        final Set<AbstractUpdateLoc> subResult = //
                abstrUpdateLocsFromTerm(t, services);
        if (!subResult.isEmpty()) {
            // We've found an atom
            return subResult;
        }

        final Set<AbstractUpdateLoc> result = new LinkedHashSet<>();
        for (Term sub : t.subs()) {
            result.addAll(extractAbstrUpdateLocsFromTerm(sub, services));
        }
        return result;
    }

    /**
     * Converts the given {@link Term} to the {@link AbstractUpdateLoc}s it is
     * representing.
     *
     * @param t
     *            The {@link Term} to extract all {@link AbstractUpdateLoc}s
     *            from.
     * @param services
     *            The {@link Services} object.
     * @return All {@link AbstractUpdateLoc}s from the given {@link Term}.
     */
    public static Set<AbstractUpdateLoc> abstrUpdateLocsFromTerm(Term t,
            Services services) {
        final Set<AbstractUpdateLoc> result = new LinkedHashSet<>();

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final SetLDT setLDT = services.getTypeConverter().getSetLDT();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();

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
        } else if (t.isRigid() && t.sort() != locSetLDT.targetSort()
                && t.sort() != heapLDT.getFieldSort()) {
            result.add(new RigidRHS(t));
        } else if (op == locSetLDT.getSingletonPV()) {
            result.addAll(abstrUpdateLocsFromTerm(t.sub(0), services));
        } else if (op == locSetLDT.getHasTo()) {
            // There is exactly one location inside a hasTo
            final AbstractUpdateLoc subResult = abstrUpdateLocsFromTerm(
                    t.sub(0), services).iterator().next();
            assert subResult instanceof AbstrUpdateLHS;
            result.add(new HasToLoc((AbstrUpdateLHS) subResult));
        } else if (op == setLDT.getSingleton()) {
            result.addAll(abstrUpdateLocsFromTerm(t.sub(0), services));
        } else if (op == locSetLDT.getSingleton()) {
            final Term obj = t.sub(0);
            final Term field = t.sub(1);
            result.add(new FieldLoc(Optional.empty(), Optional.empty(), obj,
                    fieldPVFromFieldFunc(field, services),
                    (LocationVariable) tb.getBaseHeap().op()));
        } else if (op == locSetLDT.getUnion() || op == setLDT.getUnion()) {
            result.addAll(abstrUpdateLocsFromTerm(t.sub(0), services));
            result.addAll(abstrUpdateLocsFromTerm(t.sub(1), services));
        } else if (heapLDT.isSelectOp(op) && t.subs().size() == 3
                && t.sub(2).op() == heapLDT.getArr()) {
            final Term heapTerm = t.sub(0);
            result.add(new ArrayLoc(t.sub(1), t.sub(2).sub(0)));
            result.addAll(abstrUpdateLocsFromTerm(heapTerm, services));
        } else if (heapLDT.isSelectOp(op)) {
            final Sort sort = heapLDT.getSortOfSelect(op);
            final Term heapTerm = t.sub(0);
            final Term obj = t.sub(1);
            final Term field = t.sub(2);
            result.add(new FieldLoc(Optional.of(sort), Optional.of(heapTerm),
                    obj, fieldPVFromFieldFunc(field, services),
                    (LocationVariable) tb.getBaseHeap().op()));
            result.addAll(abstrUpdateLocsFromTerm(heapTerm, services));
        } else if (op == heapLDT.getStore()) {
            final Term heapTerm = t.sub(0);
            final Term obj = t.sub(1);
            final Term field = t.sub(2);
            result.add(new FieldLoc(Optional.empty(), Optional.empty(), obj,
                    fieldPVFromFieldFunc(field, services),
                    (LocationVariable) tb.getBaseHeap().op()));
            result.addAll(abstrUpdateLocsFromTerm(heapTerm, services));
        } else {
            /*
             * TODO (DS, 2019-03-11): Debug code, remove when we're sure that
             * everything's covered.
             */
            System.out.printf(
                    "Unexpected operator \"%s\" in term \"%s\", cannot convert to AbstrUpdateLoc%n",
                    op.name(), t);
        }

        return result;
    }

    /**
     * Returns, for a term representing a field, the "canonical" field program
     * variable.
     *
     * @param field
     *            The field term, something like "my.package.Type::$field", of
     *            Sort "Field" (of {@link HeapLDT}).
     * @param services
     *            The {@link Services} object (for {@link JavaInfo} and
     *            {@link HeapLDT}).
     * @return The canonical program variable representing the field.
     */
    private static LocationVariable fieldPVFromFieldFunc(Term field,
            Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final JavaInfo javaInfo = services.getJavaInfo();
        assert field.sort() == heapLDT.getFieldSort();

        final int sepIdx = field.toString().indexOf("::$");
        assert sepIdx > 0;

        final String typeStr = field.toString().substring(0, sepIdx);
        final String fieldStr = field.toString().substring(sepIdx + 3);

        final KeYJavaType kjt = javaInfo.getKeYJavaType(typeStr);
        return (LocationVariable) javaInfo
                .getCanonicalFieldProgramVariable(fieldStr, kjt);
    }

    /**
     * Transforms a set of abstract update right-hand sides to a set union term.
     *
     * @param accessibles
     *            The accessibles (right-hand sides) to construct the union term
     *            of.
     *
     * @param services
     *            The services object.
     *
     * @return A set union term from the given accessibles.
     */
    public Term accessiblesToSetUnion(Set<AbstrUpdateRHS> accessibles,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.setUnion(accessibles.stream().map(loc -> loc.toTerm(services))
                .map(tb::setSingleton).collect(Collectors.toList()));
    }
}
