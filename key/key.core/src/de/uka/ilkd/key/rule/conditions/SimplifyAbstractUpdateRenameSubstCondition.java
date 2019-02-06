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

package de.uka.ilkd.key.rule.conditions;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractUpdate;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.AbstractExecutionUtils;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 *
 * Simplifies an update cascade like
 *
 * <pre>
 *   {... || y := t || ...}
 *     {U_P(..., y, ... := ..., y, ...)}
 *        {... || x := t || ... || x := y || ...}
 *          phi(x)
 * </pre>
 *
 * (where phi does not contain y) to
 *
 * <pre>
 *   {... || x := t || ...}
 *     {U_P(..., x, ... := ..., x, ...)}
 *        {... || ...}
 *          phi(x)
 * </pre>
 *
 * i.e. eliminates the renaming substitution "y for x". Since phi does not
 * contain y, this is sound: it holds for every concrete update you could
 * substitute for U_P.
 *
 * This relies on an initialization of the renamed variable, which also occurs
 * "clashing" in the second parallel update.
 *
 * Also, simplifies
 *
 * <pre>
 *   {... || y := t || ...}
 *     {U_P(... := ..., y, ...)}
 *        {... || x := t || ...}
 *          phi(x)
 * </pre>
 *
 * (where phi, the LHS of U_P, and the second abstract update, do not contain y)
 * to
 *
 * <pre>
 *   {... || x := t || ...}
 *     {U_P(... := ..., x, ...)}
 *        {... || ...}
 *          phi(x)
 * </pre>
 *
 * @author Dominic Steinhoefel
 */
public final class SimplifyAbstractUpdateRenameSubstCondition
        implements VariableCondition {
    private final UpdateSV u1;
    private final UpdateSV u2;
    private final UpdateSV u3;
    private final SchemaVariable phi;
    private final SchemaVariable result;

    public SimplifyAbstractUpdateRenameSubstCondition(UpdateSV u1, UpdateSV u2,
            UpdateSV u3, SchemaVariable phi, SchemaVariable result) {
        this.u1 = u1;
        this.u2 = u2;
        this.u3 = u3;
        this.phi = phi;
        this.result = result;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        final Term u1Inst = (Term) svInst.getInstantiation(u1);
        final Term u2Inst = (Term) svInst.getInstantiation(u2);
        final Term u3Inst = (Term) svInst.getInstantiation(u3);
        final Term phiInst = (Term) svInst.getInstantiation(phi);
        final Term resultInst = (Term) svInst.getInstantiation(result);

        final TermBuilder tb = services.getTermBuilder();

        if (u1Inst == null || u2Inst == null || u3Inst == null
                || phiInst == null || resultInst != null) {
            return mc;
        }

        if (!MergeRuleUtils.isUpdateNormalForm(u1Inst)
                || !MergeRuleUtils.isUpdateNormalForm(u3Inst)) {
            return null;
        }

        if (!(u2Inst.op() instanceof AbstractUpdate)) {
            /*
             * We can assume that u2Inst is abstract, but it might be
             * constructed of an update junctor. In that case, we continue here.
             * TODO (DS, 2019-05-02): We could probably generalize this to
             * concatenations, maybe do this eventually.
             */
            assert u2Inst.op() instanceof UpdateJunctor;
            return null;
        }

        final AbstractUpdate abstrUpd = (AbstractUpdate) u2Inst.op();
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final Iterable<LocationVariable> assgnVarsOfAbstrUpd = () -> abstrUpd
                .getAssignables().stream()
                .filter(t -> t.op() == locSetLDT.getSingletonPV())
                .map(t -> t.sub(0).sub(0).op())
                .map(LocationVariable.class::cast).iterator();

        final Set<LocationVariable> locVarsInPhi = //
                collectLocVars(services, phiInst);

        // Those might be changed several times
        Term newFirstConcreteUpdate = u1Inst;
        Term newAbstrUpd = u2Inst;
        Term newSecondConcreteUpdate = u3Inst;

        // Signals that we did perform a change
        boolean success = false;

        //@formatter:off
        /*
         * Find an assignable of the abstract update u2 which
         * - does not occur in phi,
         * - is initialized in u1,
         * - is a right-hand side of exactly one update "elem" in u3,
         * - such that the left-hand side of "elem" is initialized to
         *   the same term as in u1 in a prior, overridden update in u3.
         *
         * Then, perform the substitution by that left-hand side of "elem".
         */
        //@formatter:on
        for (final LocationVariable lhs : assgnVarsOfAbstrUpd) {
            /* Check that lhs does not occur in the target. */
            if (locVarsInPhi.contains(lhs)) {
                continue;
            }

            final Term u1rhs = MergeRuleUtils
                    .getUpdateRightSideFor(newFirstConcreteUpdate, lhs);
            if (u1rhs == null) {
                continue;
            }

            final List<Term> u3elems = MergeRuleUtils
                    .getElementaryUpdates(newSecondConcreteUpdate, true)
                    .stream().filter(elem -> elem.sub(0).op() == lhs)
                    .collect(Collectors.toList());
            if (u3elems.size() != 1) {
                continue;
            }
            final Term u3elem = u3elems.get(0);
            final LocationVariable substCandidate = //
                    (LocationVariable) ((ElementaryUpdate) u3elem.op()).lhs();

            if (phiInst.containsJavaBlockRecursive() && !MergeRuleUtils
                    .getElementaryUpdates(newSecondConcreteUpdate, false)
                    .stream()
                    .filter(elem -> ((ElementaryUpdate) elem.op())
                            .lhs() == substCandidate && elem.sub(0) == u1rhs)
                    .findAny().isPresent()) {
                continue;
            }

            // We found what we were looking for, now substitute.
            success = true;

            newFirstConcreteUpdate = //
                    substLHSInElementary(newFirstConcreteUpdate, lhs,
                            substCandidate, tb);
            newAbstrUpd = //
                    substLocVarInAbstractUpdate(newAbstrUpd, lhs,
                            substCandidate, services);
            newSecondConcreteUpdate = //
                    removeElementaryWithLHS(newSecondConcreteUpdate,
                            substCandidate, tb);
        }

        // TODO: Second simplification for accessibles only
        /* @formatter:off
         *
         *   {... || y := t || ...}
         *     {U_P(... := ..., y, ...)}
         *        {... || x := t || ...}
         *          phi(x)
         * to
         *
         *   {... || x := t || ...}
         *     {U_P(... := ..., x, ...)}
         *        {... || ...}
         *          phi(x)
         * @formatter:on
         */

        //@formatter:off
        /* Find an accessible of the abstract update u2 which
         * - does not occur as LHS in u2
         * - does not occur as LHS in u3
         * - does not occur in phi
         * - is initialized by some term "t" in u1 such that "t"
         *   is also the target RHS for some PV "x" in u3
         *
         * Then, substitute the (mentioned) occurrences of that accessible by x,
         * and remove the elementary update "x:=t" in u3.
         */
        //@formatter:on

        final Set<LocationVariable> accessibles = AbstractExecutionUtils
                .getAccessiblesForAbstractUpdate(newAbstrUpd).stream()
                .filter(LocationVariable.class::isInstance)
                .map(LocationVariable.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        for (final LocationVariable rhs : accessibles) {
            if (AbstractExecutionUtils
                    .getAssignablesForAbstractUpdate(newAbstrUpd)
                    .contains(rhs)) {
                continue;
            }

            if (MergeRuleUtils
                    .getUpdateLeftSideLocations(newSecondConcreteUpdate)
                    .contains(rhs)) {
                continue;
            }

            if (locVarsInPhi.contains(rhs)) {
                continue;
            }

            final Term t = MergeRuleUtils.getUpdateRightSideFor(u1Inst, rhs);
            if (t == null) {
                continue;
            }

            final List<Term> matchingElemsInU3 = MergeRuleUtils
                    .getElementaryUpdates(newSecondConcreteUpdate).stream()
                    .filter(elem -> elem.sub(0) == t)
                    .collect(Collectors.toList());
            if (matchingElemsInU3.size() != 1) {
                continue;
            }

            final LocationVariable x = //
                    (LocationVariable) ((ElementaryUpdate) matchingElemsInU3
                            .get(0).op()).lhs();

            // We have a match
            success = true;

            newFirstConcreteUpdate = //
                    substLHSInElementary(newFirstConcreteUpdate, rhs, x, tb);
            newAbstrUpd = //
                    substLocVarInAbstractUpdate(newAbstrUpd, rhs, x, services);
            newSecondConcreteUpdate = //
                    removeElementaryWithLHS(newSecondConcreteUpdate, x, tb);
        }

        if (!success) {
            return null;
        }

        final Term newResultInst = tb.apply(newFirstConcreteUpdate, tb.apply(
                newAbstrUpd, tb.apply(newSecondConcreteUpdate, phiInst)));
        svInst = svInst.add(result, newResultInst, services);
        return mc.setInstantiations(svInst);
    }

    private Term substLHSInElementary(Term u1Inst, LocationVariable lhs,
            LocationVariable substCandidate, TermBuilder tb) {
        return tb.parallel(MergeRuleUtils.getElementaryUpdates(u1Inst).stream()
                .map(elem -> {
                    if (((ElementaryUpdate) elem.op()).lhs() == lhs) {
                        return tb.elementary(substCandidate, elem.sub(0));
                    }
                    else {
                        return elem;
                    }
                }).collect(ImmutableSLList.toImmutableList()));
    }

    /**
     * Removes the elementary "lhs:=..." from the given concrete update.
     *
     * @param update
     *            The update from which to remove the elementary.
     * @param lhs
     *            The lhs of the elementary to remove.
     * @param tb
     *            {@link TermBuilder} object.
     * @return The new update.
     */
    private Term removeElementaryWithLHS(final Term update,
            final LocationVariable lhs, final TermBuilder tb) {
        final Term newConcreteUpdate = tb
                .parallel(MergeRuleUtils.getElementaryUpdates(update).stream()
                        .filter(t -> ((ElementaryUpdate) t.op()).lhs() != lhs)
                        .collect(ImmutableSLList.toImmutableList()));
        return newConcreteUpdate;
    }

    private Term substLocVarInAbstractUpdate(Term abstractUpdateTerm,
            LocationVariable lhs1, LocationVariable lhs2, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final AbstractUpdate abstrUpd = //
                (AbstractUpdate) abstractUpdateTerm.op();

        final Term oldAssignables = abstrUpd.lhs();
        final Term oldAccessibles = abstractUpdateTerm.sub(0);

        final Term newAbstrUpdLHS = //
                replaceVarInTerm(lhs1, lhs2, oldAssignables, services);

        final Term newAbstrUpdRHS = //
                replaceVarInTerm(lhs1, lhs2, oldAccessibles, services);

        return tb.abstractUpdate(abstrUpd.getAbstractPlaceholderStatement(),
                newAbstrUpdLHS, newAbstrUpdRHS);
    }

    static Term replaceVarInTerm(LocationVariable lhs1, LocationVariable lhs2,
            final Term oldAssignables, Services services) {
        final Map<LocationVariable, LocationVariable> substMap = new HashMap<>();
        substMap.put(lhs1, lhs2);
        final OpReplacer opRepl = new OpReplacer(substMap,
                services.getTermFactory());
        final Term newAbstrUpdLHS = opRepl.replace(oldAssignables);
        return newAbstrUpdLHS;
    }

    private Set<LocationVariable> collectLocVars(Services services,
            final Term xInst) {
        final OpCollector opColl = new OpCollector();
        xInst.execPostOrder(opColl);
        final Set<LocationVariable> occurringLocVars = opColl.ops().stream()
                .filter(op -> op instanceof LocationVariable)
                .map(LocationVariable.class::cast).collect(Collectors.toSet());

        if (xInst.containsJavaBlockRecursive()) {
            final JavaBlock jb = MergeRuleUtils.getJavaBlockRecursive(xInst);
            final ProgramVariableCollector pvc = new ProgramVariableCollector(
                    jb.program(), services);
            pvc.start();
            occurringLocVars.addAll(pvc.result());
        }
        return occurringLocVars;
    }

    @Override
    public String toString() {
        return String.format(
                "\\simplifyAbstractUpdateRenameSubst(%s, %s, %s, %s, %s)", //
                u1, u2, u3, phi, result);
    }
}