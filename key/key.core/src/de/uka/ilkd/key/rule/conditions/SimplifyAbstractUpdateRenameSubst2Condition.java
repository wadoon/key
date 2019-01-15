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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

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
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Simplifies an update cascade like
 *
 * <pre>
 *   {... || y := x || ...}
 *     {U_P(..., y, ... := ...)}
 *       phi(y)
 * </pre>
 *
 * (where phi does not contain x, and also not a Java block to be on the safe
 * side (TODO (DS, 2019-01-15): This restriction (Java block) is actually not
 * implemented and maybe also not necessary since we collect all variables,
 * double-check!) to
 *
 * <pre>
 *   {... || ...}
 *     {U_P(..., x, ... := ...)}
 *       phi(x)
 * </pre>
 *
 * i.e. eliminates the renaming substitution "y for x". Since phi does not
 * contain x, this is sound: it holds for every concrete update you could
 * substitute for U_P.
 *
 * @author Dominic Steinhoefel
 */
public final class SimplifyAbstractUpdateRenameSubst2Condition
        implements VariableCondition {
    private final UpdateSV concrUpdSV;
    private final UpdateSV abstrUpdSV;
    private final SchemaVariable phiSV;
    private final SchemaVariable resultSV;

    public SimplifyAbstractUpdateRenameSubst2Condition(UpdateSV concrUpdSV,
            UpdateSV abstrUpdSV, SchemaVariable phiSV,
            SchemaVariable resultSV) {
        this.concrUpdSV = concrUpdSV;
        this.abstrUpdSV = abstrUpdSV;
        this.phiSV = phiSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        final Term concrUpdInst = (Term) svInst.getInstantiation(concrUpdSV);
        final Term abstrUpdInst = (Term) svInst.getInstantiation(abstrUpdSV);
        final Term phiInst = (Term) svInst.getInstantiation(phiSV);

        /* Some basic required objects */
        final TermBuilder tb = services.getTermBuilder();
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();

        if (concrUpdInst == null || abstrUpdInst == null || phiInst == null
                || svInst.getInstantiation(resultSV) != null) {
            return mc;
        }

        if (!MergeRuleUtils.isUpdateNormalForm(concrUpdInst)) {
            return null;
        }

        if (!(abstrUpdInst.op() instanceof AbstractUpdate)) {
            /*
             * We can assume that the instantiation is abstract, but it might be
             * constructed of an update junctor.
             */
            assert abstrUpdInst.op() instanceof UpdateJunctor;
            return null;
        }

        /*
         * Find an assignable of the abstract update which is a left-hand side
         * of the concrete update, such that the corresponding right-hand side
         * in the concrete update does not appear in phi.
         */

        final AbstractUpdate abstrUpd = (AbstractUpdate) abstrUpdInst.op();
        final List<LocationVariable> relevantAssgnVarsOfAbstrUpd = abstrUpd
                .getAssignables().stream()
                .filter(t -> t.op() == locSetLDT.getSingletonPV())
                .map(t -> t.sub(0).sub(0).op())
                .map(LocationVariable.class::cast)
                .collect(Collectors.toCollection(ArrayList::new));

        /* Remove those that are not left-hand sides of the concrete update. */
        final ImmutableSet<LocationVariable> concrUpdLHSs = //
                MergeRuleUtils.getUpdateLeftSideLocations(concrUpdInst);
        relevantAssgnVarsOfAbstrUpd.removeIf(lv -> !concrUpdLHSs.contains(lv));

        /*
         * Relevant are now variables for which the RHS in the concrete update
         * is also a LocationVariable which furthermore does not appear in phi.
         */
        final Set<LocationVariable> locVarsInPhi = //
                collectLocVars(services, phiInst);

        final List<Pair<LocationVariable, LocationVariable>> potentialSubsts = //
                relevantAssgnVarsOfAbstrUpd.stream()
                        .map(lv -> new Pair<>(lv,
                                MergeRuleUtils.getUpdateRightSideFor(
                                        concrUpdInst, lv)))
                        .filter(p -> p.second.op() instanceof LocationVariable)
                        .map(p -> new Pair<>(p.first,
                                (LocationVariable) p.second.op()))
                        .filter(p -> !locVarsInPhi.contains(p.second))
                        .collect(Collectors.toList());

        if (potentialSubsts.isEmpty()) {
            return null;
        }

        /* Perform all renamings for the found substitutions. */

        Term newConcreteUpd = concrUpdInst;
        Term newAbstrUpd = abstrUpdInst;
        Term newPhiInst = phiInst;

        for (Pair<LocationVariable, LocationVariable> subst : potentialSubsts) {
            newConcreteUpd = createNewConcreteUpdate(newConcreteUpd,
                    subst.first, tb);
            newAbstrUpd = createNewAbstractUpdate(newAbstrUpd, subst.first,
                    subst.second, services);
            newPhiInst = replaceVarInTerm(newPhiInst, subst.first, subst.second,
                    services);
        }

        final Term newResultInst = //
                tb.apply(newConcreteUpd, tb.apply(newAbstrUpd, newPhiInst));

        svInst = svInst.add(resultSV, newResultInst, services);
        return mc.setInstantiations(svInst);
    }

    /**
     * Creates an update by removing the elementary which has as LHS the given
     * LocationVariable.
     *
     * @param originalUpdate
     *            The original update.
     * @param lhsToRemove
     *            The LHS to remove.
     * @param tb
     *            The {@link TermBuilder}.
     * @return A new update where the elementary with the given LHS has been
     *         removed. Might be the same update if there is no such elementary.
     */
    private Term createNewConcreteUpdate(final Term originalUpdate,
            final LocationVariable lhsToRemove, final TermBuilder tb) {
        final Term newConcreteUpdate = tb.parallel(MergeRuleUtils
                .getElementaryUpdates(originalUpdate).stream()
                .filter(t -> ((ElementaryUpdate) t.op()).lhs() != lhsToRemove)
                .collect(ImmutableSLList.toImmutableList()));
        return newConcreteUpdate;
    }

    private Term createNewAbstractUpdate(Term abstractUpdateTerm,
            LocationVariable toReplace, LocationVariable newVar,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final AbstractUpdate abstrUpd = //
                (AbstractUpdate) abstractUpdateTerm.op();

        final Term oldAssignables = abstrUpd.lhs();

        final Term newAbstrUpdLHS = //
                replaceVarInTerm(oldAssignables, toReplace, newVar, services);

        final Term newAbstrUpd = tb.abstractUpdate(
                abstrUpd.getAbstractPlaceholderStatement(), newAbstrUpdLHS,
                abstractUpdateTerm.sub(0));

        return newAbstrUpd;
    }

    static Term replaceVarInTerm(final Term replaceIn,
            LocationVariable toReplace, LocationVariable newVar,
            Services services) {
        final Map<LocationVariable, LocationVariable> substMap = new HashMap<>();
        substMap.put(toReplace, newVar);
        final OpReplacer opRepl = new OpReplacer(substMap,
                services.getTermFactory());
        final Term newAbstrUpdLHS = opRepl.replace(replaceIn);
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
                "\\simplifyAbstractUpdateRenameSubst2(%s, %s, %s, %s)", //
                concrUpdSV, abstrUpdSV, phiSV, resultSV);
    }
}