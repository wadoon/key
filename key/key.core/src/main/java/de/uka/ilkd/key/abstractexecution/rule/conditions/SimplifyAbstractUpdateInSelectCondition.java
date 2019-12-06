// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
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

import java.util.List;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.EmptyLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.IrrelevantAssignable;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Tries to simplify the given update, which is a parallel update containing
 * abstract updates or a single abstract update, that occurs in front of the
 * heap in a select term <code>any::select({U}h,o,f). If in that update, there
 * is an abstract update the frame of which definitely does not contain (o,f),
 * that abstract update is removed.
 * 
 * @author Dominic Steinhoefel
 */
public class SimplifyAbstractUpdateInSelectCondition implements VariableCondition {
    private final UpdateSV uSV;
    private final SchemaVariable oSV;
    private final SchemaVariable fSV;
    private final SchemaVariable frameSV;
    private final UpdateSV resultSV;

    public SimplifyAbstractUpdateInSelectCondition(UpdateSV uSV, SchemaVariable oSV,
            SchemaVariable fSV, SchemaVariable frameSV, UpdateSV resultSV) {
        this.uSV = uSV;
        this.oSV = oSV;
        this.fSV = fSV;
        this.frameSV = frameSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Goal goal, Services services) {

        final SVInstantiations svInst = matchCond.getInstantiations();
        final Term update = (Term) svInst.getInstantiation(uSV);
        final Term o = (Term) svInst.getInstantiation(oSV);
        final Term f = (Term) svInst.getInstantiation(fSV);
        final Term result = (Term) svInst.getInstantiation(resultSV);

        assert update != null && o != null && f != null;

        if (result != null) {
            return matchCond;
        }

        /*
         * We only consider abstract updates that are top-level in the (parallel)
         * update.
         */

        if (!(update.op() instanceof AbstractUpdate)
                && !(update.op() == UpdateJunctor.PARALLEL_UPDATE)) {
            return null;
        }

        /*
         * Drop all abstract updates in update whose frames do not include (o,f) To
         * prove this, we're looking for explicit assumptions
         * "==> elementOf(o,f,frame)".
         */

        final TermBuilder tb = services.getTermBuilder();
        final List<Term> elementaries = MergeRuleUtils.getElementaryUpdates(update, false, tb);
        ImmutableList<Term> newElementaries = ImmutableSLList.<Term>nil();

        Term chosenFrame = null;
        Term possibleFrame = null;
        for (final Term elem : elementaries) {
            if (chosenFrame == null && elem.op() instanceof AbstractUpdate) {
                possibleFrame = ((AbstractUpdate) elem.op()).getAllAssignables().stream()
                        .map(AbstractExecutionUtils::unwrapHasTo).map(loc -> loc.toTerm(services))
                        .collect(Collectors.reducing(tb.empty(), (s1, s2) -> tb.union(s1, s2)));

                if (canDropAbstractUpdate(elem, o, f, goal, services)) {
                    chosenFrame = possibleFrame;
                }

            } else {
                newElementaries = newElementaries.append(elem);
            }
        }

        if (chosenFrame == null && possibleFrame != null) {
            /*
             * Instead of returning null, we select any possible frame that could work. The
             * reason is that we want this varcond to be checked again once that there's a
             * changed assumption, because this can render the rule applicable for the same
             * find term for which it wasn't applicable before. This is still not ideal,
             * since we could miss another abstract update in a parallel one which we'd like
             * to consider. Ideal would be to revisit this condition whenever we get a new
             * assumption, that's however not how KeY works.
             */

            return matchCond.setInstantiations(svInst //
                    .add(frameSV, possibleFrame, services));
        } else if (chosenFrame == null && possibleFrame == null) {
            /* This should not happen... */
            return null;
        }

        return matchCond.setInstantiations(svInst //
                .add(resultSV, tb.parallel(newElementaries), services)
                .add(frameSV, chosenFrame, services));
    }

    /**
     * Returns true iff the given abstract update may be dropped, i.e., there is
     * evidence that its frame does not contain (o,f).
     * 
     * @param update   The abstract update to maybe drop.
     * @param o        The Object of the (o,f) location that is selected.
     * @param f        The Field of the (o,f) location that is selected.
     * @param goal     The current goal.
     * @param services The {@link Services} object.
     * 
     * @return true iff the given abstract update may be dropped, i.e., there is
     *         evidence that its frame does not contain (o,f).
     */
    private boolean canDropAbstractUpdate(final Term update, final Term o, final Term f,
            final Goal goal, final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        assert update.op() instanceof AbstractUpdate;

        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();
        final Term frame = relevantFrameFromAbstrUpd(abstrUpd, services);

        // Look for "==> elementOf(o,f,frame)"
        final Term elementOfFor = tb.elementOf(o, f, frame);
        final Term negatedElementOfFor = tb.not(tb.elementOf(o, f, frame));

        return goal.sequent().succedent().asList().stream().map(SequentFormula::formula)
                .anyMatch(sucFor -> sucFor.equalsModIrrelevantTermLabels(elementOfFor))
                || goal.sequent().antecedent().asList().stream().map(SequentFormula::formula)
                        .anyMatch(sucFor -> sucFor
                                .equalsModIrrelevantTermLabels(negatedElementOfFor));
    }

    /**
     * Creates a LocSet union {@link Term} of all abstract update assignables that
     * in principle could play a role.
     * 
     * @param abstrUpd The {@link AbstractUpdate} from which to create an assignable
     *                 union term.
     * @param services The {@link Services} object for creating {@link Term}s from
     *                 {@link AbstractUpdate}s.
     * @return The union term.
     */
    private Term relevantFrameFromAbstrUpd(final AbstractUpdate abstrUpd, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return abstrUpd.getAllAssignables().stream().map(AbstractExecutionUtils::unwrapHasTo)
                .filter(loc -> !(loc instanceof EmptyLoc))
                .filter(loc -> !(loc instanceof IrrelevantAssignable))
                .map(loc -> loc.toTerm(services))
                .collect(Collectors.reducing(tb.empty(), (s1, s2) -> tb.union(s1, s2)));
    }

    @Override
    public String toString() {
        return String.format("\\simplifyAbstractUpdateInSelect(%s, %s, %s, %s)", //
                uSV, oSV, fSV, resultSV);
    }

}
