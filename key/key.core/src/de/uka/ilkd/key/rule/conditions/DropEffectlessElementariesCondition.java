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

import java.util.Optional;
import java.util.Set;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.AbstractExecutionTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;

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
            else if (target.op() instanceof Function
                    && !target.op().isRigid()) {
                /*
                 * (DS) Special case introduced for non-rigid abstract path
                 * conditions arising from abstract execution.
                 */
                return null;
            }
            else {
                return services.getTermBuilder().skip();
            }
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
        else if (AbstractUpdateCondition.isAbstractUpdate(update)) {
            if (relevantVars.isEmpty() && target.isRigid()) {
                /*
                 * We drop abstract updates in front of rigid symbols, like
                 * "true" or some predicate, but not in front of anything
                 * containing program variables, or the special nonrigid
                 * predicates for abstract path conditions -- if there is no
                 * explicit assignable_not specification (see below).
                 */
                return services.getTermBuilder().skip();
            }

            final AbstractPlaceholderStatement abstrProg = Optional
                    .ofNullable(
                            update.getLabel(AbstractExecutionTermLabel.NAME))
                    .map(AbstractExecutionTermLabel.class::cast)
                    .map(AbstractExecutionTermLabel::getAbstrPlaceholderStmt)
                    .orElse(null);

            if (!relevantVars.isEmpty() && abstrProg != null) {
                final ImmutableSet<BlockContract> contracts = services
                        .getSpecificationRepository()
                        .getAbstractPlaceholderStatementContracts(abstrProg);

                for (final BlockContract contract : contracts) {
                    /*
                     * Try to find a contract which permits dropping the update
                     * since all the relevant variables are not assignable.
                     */
                    final Term assignableNot = contract.getAssignableNot(
                            services.getTypeConverter().getHeapLDT().getHeap());

                    /*
                     * This assignableNot term is a nested union of LocSet
                     * terms. We extract all program variables from it.
                     */
                    final TermProgramVariableCollector coll =
                            new TermProgramVariableCollector(services);
                    assignableNot.execPostOrder(coll);
                    Set<LocationVariable> notAssgnVars = coll.result();

                    /*
                     * If all the relevant variables are explicitly declared to
                     * be not assignable, we can drop this update.
                     */
                    if (relevantVars.stream().map(LocationVariable::toString)
                            .allMatch(relvar -> notAssgnVars.stream()
                                    .map(LocationVariable::toString)
                                    .anyMatch(notAssngVar -> relvar
                                            .equals(notAssngVar)))) {
                        /*
                         * TODO (DS, 2018-12-18): The above String comparison is
                         * a hack. It should actually be
                         * "notAssgnVars.containsAll(relevantVars)", but the
                         * variables in the block contract are different objects
                         * from those in the proof. Maybe we have to extend some
                         * visitor / update method or the like.
                         */
                        return services.getTermBuilder().skip();
                    }
                }
            }

            /* We cannot do anything here -- keep the abstract update. */
            return null;
        }
        else {
            return null;
        }
    }

    private static Term dropEffectlessElementaries(Term update, Term target,
            Services services) {
        if (AbstractUpdateCondition.isAbstractUpdate(target)) {
            return null;
        }

        TermProgramVariableCollector collector =
                services.getFactory().create(services);
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

        Term properResultInst =
                dropEffectlessElementaries(uInst, xInst, services);
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
}