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

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 *
 * Simplifies an update cascade like
 *
 * <pre>
 *   {U_P(..., hasTo(y), ... := ... )}
 *      {... || x := y || ...}
 *        phi(x)
 * </pre>
 *
 * (where phi does not contain y) to
 *
 * <pre>
 *   {U_P(..., hasTo(x), ... := ...)}
 *      {... || ...}
 *        phi(x)
 * </pre>
 *
 * i.e. eliminates the renaming substitution "y for x". Since phi does not
 * contain y, this is sound: it holds for every concrete update you could
 * substitute for U_P.
 *
 * @author Dominic Steinhoefel
 */
public final class ApplyAbstrOnConcrUpdateCondition
        implements VariableCondition {
    private final UpdateSV u1SV;
    private final UpdateSV u2SV;
    private final SchemaVariable phiSV;
    private final SchemaVariable resultSV;

    public ApplyAbstrOnConcrUpdateCondition(UpdateSV u1SV, UpdateSV u2SV,
            SchemaVariable phi, SchemaVariable result) {
        this.u1SV = u1SV;
        this.u2SV = u2SV;
        this.phiSV = phi;
        this.resultSV = result;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        final Term abstrUpdateTerm = (Term) svInst.getInstantiation(u1SV);
        final Term concrUpdate = (Term) svInst.getInstantiation(u2SV);
        final Term phiInst = (Term) svInst.getInstantiation(phiSV);
        final Term resultInst = (Term) svInst.getInstantiation(resultSV);

        final TermBuilder tb = services.getTermBuilder();

        if (abstrUpdateTerm == null || concrUpdate == null || phiInst == null
                || resultInst != null) {
            return mc;
        }

        if (!MergeRuleUtils.isUpdateNormalForm(concrUpdate)) {
            return null;
        }

        if (!(abstrUpdateTerm.op() instanceof AbstractUpdate)) {
            /*
             * We can assume that u2Inst is abstract, but it might be
             * constructed of an update junctor. In that case, we continue here.
             * TODO (DS, 2019-05-02): We could probably generalize this to
             * concatenations, maybe do this eventually.
             */
            assert abstrUpdateTerm.op() instanceof UpdateJunctor;
            return null;
        }

        final Set<LocationVariable> locVarsInPhi = //
                MiscTools.collectLocVars(phiInst, services);

        // Those might be changed several times
        Term newConcreteUpdate = concrUpdate;
        Term newAbstrUpd = abstrUpdateTerm;

        // Signals that we did perform a change
        boolean success = false;

        /*
         * TODO (DS, 2019-03-01): Check whether special heap handling is
         * necessary.
         */
        final AbstractUpdate abstrUpd = (AbstractUpdate) abstrUpdateTerm.op();
        final List<LocationVariable> hasToAssignableLocVars = abstrUpd
                .getHasToAssignables().stream().filter(PVLoc.class::isInstance)
                .map(PVLoc.class::cast).map(PVLoc::childOps)
                .flatMap(Collection::stream).map(LocationVariable.class::cast)
                .collect(Collectors.toList());

        //@formatter:off
        /*
         * Find a has-to assignable y of the abstract update which
         * - does not occur in phi,
         * - is no left-hand side of the concrete update.
         * - is a right-hand side of exactly one update elem
         *   "x := y" in the concrete update,
         *
         * Then, perform the substitution of y by x, and drop elem.
         */
        //@formatter:on
        for (final LocationVariable y : hasToAssignableLocVars) {
            /* Check that y does not occur in the target. */
            if (locVarsInPhi.contains(y)) {
                continue;
            }

            /* Check that y is no left-hand side of the concrete update */
            if (MergeRuleUtils.getUpdateLeftSideLocations(newConcreteUpdate,
                    services.getTermBuilder()).contains(y)) {
                continue;
            }

            /*
             * Check that y is a right-hand side of exactly one update elem
             * "x := y" in the concrete update.
             */
            final List<Term> concrUpdateElems = MergeRuleUtils
                    .getElementaryUpdates(newConcreteUpdate,
                            services.getTermBuilder())
                    .stream().filter(elem -> elem.sub(0).op() == y)
                    .collect(Collectors.toList());
            if (concrUpdateElems.size() != 1) {
                continue;
            }

            final Term elem = concrUpdateElems.get(0);
            final LocationVariable x = //
                    (LocationVariable) ((ElementaryUpdate) elem.op()).lhs();

            // We found what we were looking for, now substitute.
            success = true;

            newAbstrUpd = //
                    substLocVarInAbstractUpdate(newAbstrUpd, y, x, services);
            newConcreteUpdate = //
                    removeElementaryWithLHS(newConcreteUpdate, x, tb);
        }

        if (!success) {
            return null;
        }

        final Term newResultInst = tb.apply(newAbstrUpd,
                tb.apply(newConcreteUpdate, phiInst));
        svInst = svInst.add(resultSV, newResultInst, services);
        return mc.setInstantiations(svInst);
    }

    /**
     * Removes the elementary "lhs:=..." from the given concrete update.
     *
     * @param update
     *     The update from which to remove the elementary.
     * @param lhs
     *     The lhs of the elementary to remove.
     * @param tb
     *     {@link TermBuilder} object.
     * @return The new update.
     */
    private Term removeElementaryWithLHS(final Term update,
            final LocationVariable lhs, final TermBuilder tb) {
        final Term newConcreteUpdate = tb.parallel(
                MergeRuleUtils.getElementaryUpdates(update, tb).stream()
                        .filter(t -> ((ElementaryUpdate) t.op()).lhs() != lhs)
                        .collect(ImmutableSLList.toImmutableList()));
        return newConcreteUpdate;
    }

    private static Term substLocVarInAbstractUpdate(Term abstractUpdateTerm,
            LocationVariable lhs1, LocationVariable lhs2, Services services) {
//        final TermBuilder tb = services.getTermBuilder();
        final TermFactory tf = services.getTermFactory();
        final AbstractUpdate abstrUpd = //
                (AbstractUpdate) abstractUpdateTerm.op();

        final AbstractUpdate newAbstrUpd = services.abstractUpdateFactory()
                .changeAssignables(abstrUpd,
                        Collections.singletonMap(lhs1, lhs2), services);

//        final Term newAbstrUpdRHS = //
//                MiscTools.replaceVarInTerm(lhs1, tb.var(lhs2),
//                        abstractUpdateTerm.sub(0), services);
        
        final Term newAbstrUpdRHS = abstractUpdateTerm.sub(0);

        return tf.createTerm(newAbstrUpd, newAbstrUpdRHS);
    }

    @Override
    public String toString() {
        return String.format("\\applyAbstrOnConcrUpdate(%s, %s, %s, %s)", //
                u1SV, u2SV, phiSV, resultSV);
    }
}