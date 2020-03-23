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
package de.uka.ilkd.key.abstractexecution.rule;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.EmptyLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.IrrelevantAssignable;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.FieldLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * {@link RuleApp} for the {@link DropAbstractUpdateInSelectRule}.
 * 
 * @author Dominic Steinhoefel
 */
public class DropAbstractUpdateInSelectRuleApp extends DefaultBuiltInRuleApp {
    private ImmutableList<PosInOccurrence> ifInsts = ImmutableSLList.<PosInOccurrence>nil();
    private boolean complete = false;
    private Optional<Term> simplifiedTerm = Optional.empty();

    // ///////////////////////////////////////////////// //
    // //////////////// PUBLIC INTERFACE /////////////// //
    // ///////////////////////////////////////////////// //

    public DropAbstractUpdateInSelectRuleApp(BuiltInRule builtInRule, PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    public DropAbstractUpdateInSelectRuleApp(BuiltInRule builtInRule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts) {
        super(builtInRule, pio, ifInsts);
        this.ifInsts = ifInsts;
    }

    @Override
    public boolean complete() {
        return complete && super.complete();
    }

    @Override
    public ImmutableList<PosInOccurrence> ifInsts() {
        return ifInsts;
    }

    /**
     * @return the simplified {@link Term}, if any. Should be present iff
     *         {@link #complete()} is true.
     */
    public Optional<Term> getSimplifiedTerm() {
        return simplifiedTerm;
    }

    @Override
    public DropAbstractUpdateInSelectRuleApp tryToInstantiate(Goal goal) {
        ifInsts = ImmutableSLList.<PosInOccurrence>nil();
        simplifiedTerm = Optional.empty();
        complete = false;

        final Services services = goal.proof().getServices();
        final TermBuilder tb = services.getTermBuilder();

        // \find(G::select({... || U_P(...:=...) || ...}h, o, f))

        final Term t = pio.subTerm();
        final Term o = pio.subTerm().sub(1);
        final Term f = pio.subTerm().sub(2);

        final List<Term> elementaries = MergeRuleUtils.getElementaryUpdates(
                UpdateApplication.getUpdate(t.sub(0)), false, services.getTermBuilder());
        ImmutableList<Term> newElementaries = ImmutableSLList.<Term>nil();

        boolean success = false;
        for (final Term elem : elementaries) {
            if (elem.op() instanceof AbstractUpdate) {
                final AbstractUpdate abstrUpd = (AbstractUpdate) elem.op();
                final Optional<ImmutableList<PosInOccurrence>> canDropResult = //
                        canDropAbstractUpdate(abstrUpd, o, f, goal, services);

                if (canDropResult.isPresent()) {
                    ifInsts = ifInsts.append(canDropResult.get());
                    success = true;
                }
            } else {
                newElementaries = newElementaries.append(elem);
            }
        }

        if (success) {
            complete = true;
            final Term newUpdateTerm = tb.apply(tb.parallel(newElementaries),
                    UpdateApplication.getTarget(t.sub(0)));
            simplifiedTerm = Optional.of( //
                    tb.tf().createTerm(t.op(), new Term[] { newUpdateTerm, o, f }, t.boundVars(),
                            t.javaBlock(), t.getLabels()));
        } else {
            ifInsts = ImmutableSLList.<PosInOccurrence>nil();
        }

        return this;
    }

    // ///////////////////////////////////////////////// //
    // //////////////// PRIVATE METHODS //////////////// //
    // ///////////////////////////////////////////////// //

    /**
     * Returns true iff the given abstract update may be dropped, i.e., there is
     * evidence that its frame does not contain (o,f).
     * 
     * @param abstrUpd The abstract update to maybe drop.
     * @param o        The Object of the (o,f) location that is selected.
     * @param f        The Field of the (o,f) location that is selected.
     * @param goal     The current goal.
     * @param services The {@link Services} object.
     * 
     * @return true iff the given abstract update may be dropped, i.e., there is
     *         evidence that its frame does not contain (o,f).
     */
    private Optional<ImmutableList<PosInOccurrence>> canDropAbstractUpdate(
            final AbstractUpdate abstrUpd, final Term o, final Term f, final Goal goal,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<PosInOccurrence> result = ImmutableSLList.<PosInOccurrence>nil();

        final List<Term> frames = abstrUpd.getAllAssignables().stream()
                .map(AbstractExecutionUtils::unwrapHasTo)
                .filter(loc -> !(loc instanceof IrrelevantAssignable))
                .filter(loc -> !(loc instanceof EmptyLoc)).map(loc -> loc.toTerm(services))
                .collect(Collectors.toList());

        for (final Term frame : frames) {
            // Check whether frame is concrete and disjoint from (o,f)

            final Set<AbstractUpdateLoc> frameLocs = AbstractUpdateFactory
                    .abstrUpdateLocsFromUnionTerm(frame, Optional.empty(), services);

            final boolean triviallyIrrelevant = frameLocs.stream()
                    .map(AbstractExecutionUtils::unwrapHasTo)
                    .allMatch(loc -> loc instanceof EmptyLoc || loc instanceof IrrelevantAssignable
                            || (loc instanceof PVLoc && ((PVLoc) loc).getVar() != services
                                    .getTypeConverter().getHeapLDT().getHeap())
                            || (loc instanceof FieldLoc
                                    && ((FieldLoc) loc).getFieldTerm().op() != f.op()));

            if (triviallyIrrelevant) {
                continue;
            }

            // Look for "==> elementOf(o,f,frame)"

            final Term elementOfFor = tb.elementOf(o, f, frame);
            final Optional<PosInOccurrence> foundInSucc = lookForFor(elementOfFor, goal, false);
            if (foundInSucc.isPresent()) {
                result = result.append(foundInSucc.get());
                continue;
            }

            final Optional<PosInOccurrence> foundInAntec = //
                    lookForFor(tb.not(tb.elementOf(o, f, frame)), goal, true);
            if (foundInAntec.isPresent()) {
                result = result.append(foundInAntec.get());
                continue;
            }

            return Optional.empty();
        }

        return Optional.of(result);
    }

    /**
     * Looks for a formula either in the antecedent or succedent, and if found,
     * returns the {@link PosInOccurrence} object for the formula as evidence.
     * 
     * @param lookFor The (top-level) formula to look for.
     * @param goal    The goal in which to look.
     * @param inAntec true iff we should look in the antecedent.
     * @return The {@link PosInOccurrence} as evidence, or an empty
     *         {@link Optional}.
     */
    private Optional<PosInOccurrence> lookForFor(final Term lookFor, final Goal goal,
            final boolean inAntec) {
        if ((inAntec ? goal.sequent().antecedent() : goal.sequent().succedent()).asList().stream()
                .map(SequentFormula::formula)
                .anyMatch(sucFor -> sucFor.equalsModIrrelevantTermLabels(lookFor))) {
            return Optional.of(new PosInOccurrence(new SequentFormula(lookFor),
                    PosInTerm.getTopLevel(), inAntec));
        } else {
            return Optional.empty();
        }
    }
}
