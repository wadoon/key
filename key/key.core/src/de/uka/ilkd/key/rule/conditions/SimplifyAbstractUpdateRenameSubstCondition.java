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
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 *
 * Simplifies an update cascade like
 *
 * <pre>
 *   {U_P(..., y, ... := ...)}
 *      {... || x := y || ...}
 *        phi
 * </pre>
 *
 * (where phi does not contain y, and also not a Java block to be on the safe
 * side) to
 *
 * <pre>
 *   {U_P(..., x, ... := ...)}
 *      {... || ...}
 *        phi
 * </pre>
 *
 * i.e. eliminates the renaming substitution "y for x". Since phi does not
 * contain y, this is sound: it holds for every concrete update you could
 * substitute for U_P.
 *
 * @author Dominic Steinhoefel
 */
public final class SimplifyAbstractUpdateRenameSubstCondition
        implements VariableCondition {
    private final UpdateSV u1;
    private final UpdateSV u2;
    private final SchemaVariable x;
    private final SchemaVariable result;

    public SimplifyAbstractUpdateRenameSubstCondition(UpdateSV u1, UpdateSV u2,
            SchemaVariable x, SchemaVariable result) {
        this.u1 = u1;
        this.u2 = u2;
        this.x = x;
        this.result = result;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        final Term u1Inst = (Term) svInst.getInstantiation(u1);
        final Term u2Inst = (Term) svInst.getInstantiation(u2);
        final Term xInst = (Term) svInst.getInstantiation(x);
        final Term resultInst = (Term) svInst.getInstantiation(result);

        final TermBuilder tb = services.getTermBuilder();

        if (u1Inst == null || u2Inst == null || xInst == null
                || resultInst != null) {
            return mc;
        }

        if (!MergeRuleUtils.isUpdateNormalForm(u2Inst)) {
            return null;
        }

        /*
         * Find an assignable of the abstract update u1 which is a right-hand
         * side of u1 and not used in xInst.
         */

        final AbstractUpdate abstrUpd = (AbstractUpdate) u1Inst.op();
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final Iterable<LocationVariable> assgnVarsOfAbstrUpd = () -> abstrUpd
                .getAssignables().stream()
                .filter(t -> t.op() == locSetLDT.getSingletonPV())
                .map(t -> t.sub(0).sub(0).op())
                .map(LocationVariable.class::cast).iterator();

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

        for (LocationVariable lhs : assgnVarsOfAbstrUpd) {
            /* Check that lhs does not occur in the target. */
            if (occurringLocVars.contains(lhs)) {
                continue;
            }

            final List<LocationVariable> potentialSubstCandidates = //
                    MergeRuleUtils.getUpdateLeftSideLocations(u2Inst).stream()
                            .filter(lhs2 -> MergeRuleUtils
                                    .getUpdateRightSideFor(u2Inst, lhs2)
                                    .op() == lhs)
                            .collect(Collectors.toList());

            /*
             * There has to be exactly one candidate for this simplification to
             * work.
             */

            if (potentialSubstCandidates.size() != 1) {
                continue;
            }

            final LocationVariable lhs2 = potentialSubstCandidates.get(0);

            /* Create the new abstract update */
            final Map<LocationVariable, LocationVariable> substMap = new HashMap<>();
            substMap.put(lhs, lhs2);
            final OpReplacer opRepl = new OpReplacer(substMap,
                    services.getTermFactory());
            final Term newAbstrUpdLHS = opRepl.replace(abstrUpd.lhs());
            final Term newAbstrUpd = tb.abstractUpdate(
                    abstrUpd.getAbstractPlaceholderStatement(), newAbstrUpdLHS,
                    u1Inst.sub(0));

            /* Create the new concrete update */
            final Term newConcreteUpdate = tb.parallel(MergeRuleUtils
                    .getElementaryUpdates(u2Inst).stream()
                    .filter(t -> ((ElementaryUpdate) t.op()).lhs() != lhs2)
                    .collect(ImmutableSLList.toImmutableList()));

            final Term newResultInst = tb.apply(newAbstrUpd,
                    tb.apply(newConcreteUpdate, xInst));

            svInst = svInst.add(result, newResultInst, services);
            return mc.setInstantiations(svInst);
        }

        return null;
    }

    @Override
    public String toString() {
        return String.format(
                "\\simplifyAbstractUpdateRenameSubst(%s, %s, %s, %s)", //
                u1, u2, x, result);
    }
}