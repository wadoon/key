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

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractUpdate;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

public final class DropEffectlessElementariesCondition
        implements VariableCondition {
    private final UpdateSV u;
    private final SchemaVariable x;
    private final SchemaVariable result;

    public DropEffectlessElementariesCondition(UpdateSV u, SchemaVariable x,
            SchemaVariable x2) {
        this.u = u;
        this.x = x;
        this.result = x2;
    }

    private static Term dropEffectlessElementariesHelper(Term update,
            Term target, Set<LocationVariable> relevantVars,
            Services services) {
        if (update.op() instanceof ElementaryUpdate) {
            ElementaryUpdate eu = (ElementaryUpdate) update.op();
            LocationVariable lhs = (LocationVariable) eu.lhs();
            if (relevantVars.contains(lhs)) {
                relevantVars.remove(lhs);
                // removed, see bug #1269 (MU, CS)
                // updates of the form "x:=x" can be discarded (MU,CS)
                //@formatter:off
//                if (lhs.equals(update.sub(0).op())) {
//                    return TB.skip();
//                }
                //@formatter:on
                return null;
            }
            /*
             * TODO (DS, 2019-01-03): Dropped this since it's too restrictive;
             * however, we have to add special treatment for the allLocs
             * location set, which has to prevent dropping *anything*!
             */
            //@formatter:off
            // else if (containsNonRigidFunctionSymbols(target)) {
            //     /*
            //      * (DS) Special case introduced for non-rigid abstract path
            //      * conditions arising from abstract execution.
            //      */
            //     return null;
            // }
            //@formatter:on
            else {
                /*
                 * In the standard case, we can drop the update here. However,
                 * if the target contains abstract programs that might access
                 * the left-hand-side of this update, we have to keep it.
                 */
                if (!containsAbstractStatementUsingLHS(target, lhs, services)) {
                    return services.getTermBuilder().skip();
                }
                else {
                    return null;
                }
            }
        }
        else if (update.op() instanceof AbstractUpdate) {
            final TermBuilder tb = services.getTermBuilder();
            final LocSetLDT locSetLDT = services.getTypeConverter()
                    .getLocSetLDT();

            final AbstractUpdate oldUpdate = (AbstractUpdate) update.op();
            final List<Term> assignables = oldUpdate.getAssignables();

            /*
             * TODO (DS, 2019-01-03): There might also be fields in the loc set,
             * we might have to eventually consider this. As of now, there are
             * no examples for this case...
             */
            final List<Term> relevantAssignables = assignables.stream()
                    .filter(t -> t.op() != locSetLDT.getSingletonPV()
                            || relevantVars.contains(t.sub(0).sub(0).op()))
                    .collect(Collectors.toList());

            relevantVars.removeAll(relevantAssignables.stream()
                    .filter(t -> t.op() == locSetLDT.getSingletonPV())
                    .map(t -> t.sub(0).sub(0)).map(Term::op)
                    .map(LocationVariable.class::cast)
                    .collect(Collectors.toList()));

            if (assignables.size() == relevantAssignables.size()) {
                return null;
            }

            return services.getTermBuilder().abstractUpdate(
                    oldUpdate.getAbstractPlaceholderStatement(),
                    tb.union(relevantAssignables), update.sub(0));
        }
        else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
            Term sub0 = update.sub(0);
            Term sub1 = update.sub(1);
            /*
             * first descend to the second sub-update to keep relevantVars in
             * good order
             */
            Term newSub1 = dropEffectlessElementariesHelper(sub1, target,
                    relevantVars, services);
            Term newSub0 = dropEffectlessElementariesHelper(sub0, target,
                    relevantVars, services);
            if (newSub0 == null && newSub1 == null) {
                return null;
            }
            else {
                newSub0 = newSub0 == null ? sub0 : newSub0;
                newSub1 = newSub1 == null ? sub1 : newSub1;
                return services.getTermBuilder().parallel(newSub0, newSub1);
            }
        }
        else if (update.op() == UpdateApplication.UPDATE_APPLICATION) {
            Term sub0 = update.sub(0);
            Term sub1 = update.sub(1);
            Term newSub1 = dropEffectlessElementariesHelper(sub1, target,
                    relevantVars, services);
            return newSub1 == null ? null
                    : services.getTermBuilder().apply(sub0, newSub1, null);
        }
        else {
            return null;
        }
    }

    private static Term dropEffectlessElementaries(Term update, Term target,
            Services services) {
        TermProgramVariableCollector collector = services.getFactory()
                .create(services);
        target.execPostOrder(collector);
        Set<LocationVariable> varsInTarget = collector.result();
        Term simplifiedUpdate = dropEffectlessElementariesHelper(update, target,
                varsInTarget, services);
        return simplifiedUpdate == null ? null
                : services.getTermBuilder().apply(simplifiedUpdate, target,
                        null);
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        Term uInst = (Term) svInst.getInstantiation(u);
        Term xInst = (Term) svInst.getInstantiation(x);
        Term resultInst = (Term) svInst.getInstantiation(result);
        if (uInst == null || xInst == null) {
            return mc;
        }

        Term properResultInst = dropEffectlessElementaries(uInst, xInst,
                services);
        if (properResultInst == null) {
            return null;
        }
        else if (resultInst == null) {
            svInst = svInst.add(result, properResultInst, services);
            return mc.setInstantiations(svInst);
        }
        else if (resultInst.equals(properResultInst)) {
            return mc;
        }
        else {
            return null;
        }
    }

    @Override
    public String toString() {
        return "\\dropEffectlessElementaries(" + u + ", " + x + ", " + result
                + ")";
    }

    private static boolean containsAbstractStatementUsingLHS(Term target,
            LocationVariable lhs, Services services) {
        final ContainsAbstractStatementUsingLHSVisitor visitor = new ContainsAbstractStatementUsingLHSVisitor(
                MergeRuleUtils.getJavaBlockRecursive(target).program(), lhs,
                services);
        visitor.start();
        final boolean containsAbstractStatementUsingLHS = visitor.result();
        return containsAbstractStatementUsingLHS;
    }

    private static boolean containsNonRigidFunctionSymbols(Term target) {
        final OpCollector opCollector = new OpCollector();
        target.execPostOrder(opCollector);
        final boolean containsNonRigidFuncSymbs = opCollector.ops().stream()
                .anyMatch(op -> op instanceof Function && !op.isRigid());
        return containsNonRigidFuncSymbs;
    }

    private static class ContainsAbstractStatementUsingLHSVisitor
            extends JavaASTVisitor {
        final LocationVariable lhs;
        boolean result = false;

        public ContainsAbstractStatementUsingLHSVisitor(ProgramElement root,
                LocationVariable lhs, Services services) {
            super(root, services);
            this.lhs = lhs;
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof AbstractPlaceholderStatement) {
                result = true;
                /*
                 * TODO (DS, 2018-12-20): Check whether that statement may use
                 * this lhs, i.e. whether it's accessible.
                 */
            }
        }

        public boolean result() {
            return result;
        }
    }
}