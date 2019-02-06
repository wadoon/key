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
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
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
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.AbstractExecutionUtils;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Simplifies an update cascade like
 *
 * <pre>
 *     {x1 := t1 || x2 := y || ...}
 *       {U_P(..., x1, ... := ... \cup x2 \cup ...)}
 *         phi
 * </pre>
 *
 * to
 *
 * <pre>
 *     {x1 := t1 || ...}
 *       {U_P(..., x1, ... := ... \cup y \cup ...)}
 *         {x2 := y}
 *           phi
 * </pre>
 *
 * i.e. applies variable assignments to the accessibles of the abstract update
 * and pushes through elementaries that are not assigned by the abstract update.
 *
 * @author Dominic Steinhoefel
 */
public final class SequentialUpdateSimplAbstrCondition
        implements VariableCondition {
    private final UpdateSV u1;
    private final UpdateSV u2;
    private final SchemaVariable x;
    private final SchemaVariable result;

    public SequentialUpdateSimplAbstrCondition(UpdateSV u1, UpdateSV u2,
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

        if (u1Inst == null || u2Inst == null || xInst == null
                || resultInst != null) {
            return mc;
        }

        final TermBuilder tb = services.getTermBuilder();

        if (!MergeRuleUtils.isUpdateNormalForm(u1Inst)) {
            return null;
        }

        if (!(u2Inst.op() instanceof AbstractUpdate)) {
            /*
             * We can assume that u1Inst is abstract, but it might be
             * constructed of an update junctor. In that case, we continue here.
             */
            assert u2Inst.op() instanceof UpdateJunctor;
            return null;
        }

        final AbstractUpdate abstrUpd = (AbstractUpdate) u2Inst.op();

        if (AbstractExecutionUtils.assignsAllLocs(abstrUpd, services)
                || AbstractExecutionUtils.accessesAllLocs(u2Inst, services)) {
            /*
             * For this case (U(allLocs:=...) / U(...:=allLocs)) we may not do
             * anything.
             */
            return null;
        }

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final Set<LocationVariable> assgnVarsOfAbstrUpd = abstrUpd
                .getAssignables().stream()
                .filter(t -> t.op() == locSetLDT.getSingletonPV())
                .map(t -> t.sub(0).sub(0).op())
                .map(LocationVariable.class::cast).collect(Collectors.toSet());

        List<Term> currentConcrUpdElems = MergeRuleUtils
                .getElementaryUpdates(u1Inst);
        Term currentAccessibles = u2Inst.sub(0);
        List<Term> currentNewConcrUpdElems = new ArrayList<>();

        for (LocationVariable lhs : MergeRuleUtils
                .getUpdateLeftSideLocations(u1Inst)) {
            if (assgnVarsOfAbstrUpd.contains(lhs)) {
                continue;
            }

            final Term rhs = MergeRuleUtils.getUpdateRightSideFor(u1Inst, lhs);

            if (rhs.op() instanceof LocationVariable) {
                currentAccessibles = SimplifyAbstractUpdateRenameSubstCondition
                        .replaceVarInTerm(lhs, (LocationVariable) rhs.op(),
                                currentAccessibles, services);
            }
            else {
                /*
                 * If lhs is contained in the accessibles, but its rhs is not a
                 * location variable, we cannot substitute it (rhs is a literal
                 * or something, but not a location), but also not push it
                 * through -- that would be unsound. Therefore, we will skip in
                 * that case.
                 */
                final OpCollector opColl = new OpCollector();
                currentAccessibles.execPostOrder(opColl);
                if (opColl.contains(lhs)) {
                    continue;
                }
            }

            currentNewConcrUpdElems.add(currentConcrUpdElems.stream()
                    .filter(t -> ((ElementaryUpdate) t.op()).lhs() == lhs)
                    .findFirst().orElseThrow());
            currentConcrUpdElems
                    .removeIf(t -> ((ElementaryUpdate) t.op()).lhs() == lhs);
        }

        final Term newAbstrUpdTerm = tb.abstractUpdate(
                abstrUpd.getAbstractPlaceholderStatement(), abstrUpd.lhs(),
                currentAccessibles);

        final Term newFirstConcrUpdate = tb.parallel(currentConcrUpdElems
                .stream().collect(ImmutableSLList.toImmutableList()));

        final Term newSecondConcrUpdate = tb.parallel(currentNewConcrUpdElems
                .stream().collect(ImmutableSLList.toImmutableList()));

        final Term newResultInst = //
                tb.apply(newFirstConcrUpdate, //
                        tb.apply(newAbstrUpdTerm,
                                tb.apply(newSecondConcrUpdate, xInst)));

        if (!newAbstrUpdTerm.op().equals(abstrUpd)
                || !newFirstConcrUpdate.equals(u1Inst)
                || !newSecondConcrUpdate.equals(tb.skip())) {
            svInst = svInst.add(result, newResultInst, services);
            return mc.setInstantiations(svInst);
        }

        return null;
    }

    @Override
    public String toString() {
        return String.format("\\sequentialUpdateSimplAbstr(%s, %s, %s, %s)", //
                u1, u2, x, result);
    }
}