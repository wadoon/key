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

import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.proof.TermAccessibleLocationsCollector;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * {@link RuleApp} for the {@link DropAnonAbstractRule}.
 * 
 * @author Dominic Steinhoefel
 */
public class DropAnonAbstractRuleApp extends DefaultBuiltInRuleApp {
    private ImmutableList<PosInOccurrence> ifInsts = ImmutableSLList.<PosInOccurrence>nil();
    private boolean complete = false;
    private Optional<Term> simplifiedTerm = Optional.empty();

    // ///////////////////////////////////////////////// //
    // //////////////// PUBLIC INTERFACE /////////////// //
    // ///////////////////////////////////////////////// //

    public DropAnonAbstractRuleApp(BuiltInRule builtInRule, PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    public DropAnonAbstractRuleApp(BuiltInRule builtInRule, PosInOccurrence pio,
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
    public DropAnonAbstractRuleApp tryToInstantiate(Goal goal) {
        ifInsts = ImmutableSLList.<PosInOccurrence>nil();
        simplifiedTerm = Optional.empty();
        complete = false;

        final Services services = goal.proof().getServices();
        final TermBuilder tb = services.getTermBuilder();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable heapVar = heapLDT.getHeap();

        // \find({ ... || heap:=anon(...) || ...} phi(value(...)))

        final Term t = pio.subTerm();
        final Term update = UpdateApplication.getUpdate(t);
        final Term target = UpdateApplication.getTarget(t);

        final TermAccessibleLocationsCollector collector = //
                new TermAccessibleLocationsCollector(//
                        goal.getLocalSpecificationRepository(), services);
        target.execPostOrder(collector);

        final List<Term> elementaries = MergeRuleUtils.getElementaryUpdates(update, false,
                services.getTermBuilder());
        ImmutableList<Term> newElementaries = ImmutableSLList.<Term>nil();

        boolean success = false;
        for (final Term elem : elementaries) {
            if (elem.op() instanceof ElementaryUpdate
                    && ((ElementaryUpdate) elem.op()).lhs() == heapVar) {

                final Optional<Pair<ImmutableList<PosInOccurrence>, Term>> tryDropResult = //
                        tryDropAnon(elem.sub(0), collector.locations(), goal);

                if (tryDropResult.isPresent()) {
                    ifInsts = ifInsts.append(tryDropResult.get().first);
                    newElementaries = newElementaries
                            .append(tb.elementary(heapVar, tryDropResult.get().second));
                    success = true;
                }
            } else {
                newElementaries = newElementaries.append(elem);
            }
        }

        if (success) {
            complete = true;
            simplifiedTerm = Optional.of(tb.apply(tb.parallel(newElementaries), target));
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
    private Optional<Pair<ImmutableList<PosInOccurrence>, Term>> tryDropAnon(final Term anonTerm,
            final Set<AbstractUpdateLoc> relevantLocs, final Goal goal) {
        final Services services = goal.proof().getServices();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<PosInOccurrence> resultEvidence = ImmutableSLList.nil();
        Term resultTerm = null;

        if (anonTerm.op() != heapLDT.getAnon()) {
            return Optional.empty();
        }

        boolean success = true;
        for (final AbstractUpdateLoc anonLoc : AbstractUpdateFactory
                .abstrUpdateLocsFromUnionTerm(anonTerm.sub(1), Optional.empty(), services)) {
            final ImmutableList<PosInOccurrence> evidence = AbstractExecutionUtils
                    .isRelevant(anonLoc, relevantLocs, Collections.emptySet(), goal, services);

            if (evidence == null) {
                resultEvidence = ImmutableSLList.<PosInOccurrence>nil();
                success = false;
                break;
            }

            resultEvidence = resultEvidence.append(evidence);
        }

        final Optional<Pair<ImmutableList<PosInOccurrence>, Term>> subResult = //
                tryDropAnon(anonTerm.sub(0), relevantLocs, goal);

        if (!success && !subResult.isPresent()) {
            return Optional.empty();
        }

        if (!success && subResult.isPresent()) {
            resultEvidence = subResult.get().first;
            resultTerm = tb.anon(subResult.get().second, anonTerm.sub(1), anonTerm.sub(2));
        } else if (success && !subResult.isPresent()) {
            resultTerm = anonTerm.sub(0);
        } else if (success && subResult.isPresent()) {
            resultEvidence = resultEvidence.append(subResult.get().first);
            resultTerm = subResult.get().second;
        }

        return Optional.of(new Pair<>(resultEvidence, resultTerm));
    }
}
