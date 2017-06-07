// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.util;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.Pair;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class LogicUtilities {

    /**
     * TODO
     * 
     * @param services
     * @param pm
     * @param origHeapTerm
     * @return
     */
    public static Optional<Pair<Term, List<Term>>> extractStoreEqsAndInnerHeapTerm(
            Services services, final IProgramMethod pm,
            final Term origHeapTerm) {
        if (origHeapTerm == null) {
            return Optional.empty();
        }

        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();

        final List<Term> storeEqualities = new ArrayList<>();
        Term innerHeapTerm = origHeapTerm;
        if (!pm.isStatic()) {
            // TODO Should we also check whether pm is pure? How to do this?

            // TODO: Is it justified to assume that a heap is of the form
            // store(store(...(anon/heap...))), i.e. if there is a store,
            // then we have a store sequence at the beginning?
            Term currHeapTerm = innerHeapTerm;
            while (currHeapTerm.op() == heapLDT.getStore()) {
                final Term targetObj = currHeapTerm.sub(1);
                final Term field = currHeapTerm.sub(2);
                final Term value = currHeapTerm.sub(3);

                // Note: value could contain method-local variables, in which
                // case the fact is likely to be uncovered by the post
                // condition. Still, we don't remove it, since then indeed, this
                // reflects behavior that is not shown to the outside, and thus
                // indicates that we're not using the strongest possible post
                // condition.

                storeEqualities.add(tb.equals(tb.select(value.sort(),
                        tb.getBaseHeap(), targetObj, field), value));

                currHeapTerm = currHeapTerm.sub(0);
            }

            // Here, currHeapTerm should be the "core" without any stores.
            innerHeapTerm = currHeapTerm;
        }

        return Optional
                .of(new Pair<Term, List<Term>>(innerHeapTerm, storeEqualities));
    }

    /**
     * TODO
     * 
     * @param services
     * @return
     */
    public static FunctionalOperationContract getFOContract(Services services) {
        final ContractPO contractPO = services.getSpecificationRepository()
                .getContractPOForProof(services.getProof());
        assert contractPO != null
                && contractPO instanceof FunctionalOperationContractPO;
        final FunctionalOperationContract fContract = //
                ((FunctionalOperationContractPO) contractPO).getContract();
        return fContract;
    }

    /**
     * TODO
     * 
     * @param pio
     * @param services
     * @return
     */
    public static Optional<LocationVariable> retrieveLoopScopeIndex(
            PosInOccurrence pio, Services services) {
        final Optional<LocationVariable> failedResult = Optional.empty();

        final Term formula;
        if (pio == null //
                || !pio.isTopLevel() //
                || (formula = pio.subTerm()).containsJavaBlockRecursive()
                || !(formula.op() instanceof UpdateApplication)) {
            return failedResult;
        }

        // @formatter:off
        
        // Expected structure:
        // {U}((x<<loopScopeIndex>> = TRUE  -> ...) & 
        //      x<<loopScopeIndex>> = FALSE -> ...)
        
        // @formatter:on

        final Term updateTarget = formula.sub(1);

        if (updateTarget.op() != Junctor.AND
                || updateTarget.sub(0).op() != Junctor.IMP
                || updateTarget.sub(1).op() != Junctor.IMP
                || updateTarget.sub(0).sub(0).op() != Equality.EQUALS
                || updateTarget.sub(1).sub(0).op() != Junctor.NOT
                || updateTarget.sub(1).sub(0).sub(0).op() != Equality.EQUALS) {
            return failedResult;
        }

        final Term loopScopeVar = updateTarget.sub(0).sub(0).sub(0);
        final Term negatedLoopScopeVar = updateTarget.sub(0).sub(0).sub(0);

        if (!(loopScopeVar.op() instanceof LocationVariable)
                || !loopScopeVar.hasLabels()
                || loopScopeVar.getLabel(
                        ParameterlessTermLabel.LOOP_SCOPE_INDEX_LABEL_NAME) == null
                || loopScopeVar != negatedLoopScopeVar) {
            return failedResult;
        }

        return Optional.of((LocationVariable) loopScopeVar.op());
    }

    /**
     * TODO
     * 
     * @param pio
     * @param analysisGoal
     * @param fact
     * @param descr
     */
    public static void prepareGoal(final PosInOccurrence pio,
            final Goal analysisGoal, final Term fact, final String descr) {
        final Services services = analysisGoal.proof().getServices();

        analysisGoal.setBranchLabel(String.format("%s \"%s\"", descr,
                LogicPrinter
                        .quickPrintTerm(TermBuilder.goBelowUpdates(fact),
                                services)
                        .replaceAll("(\\r|\\n|\\r\\n)+", "")
                        .replaceAll("<<[^>]+>>", "").trim()));

        analysisGoal.removeFormula(pio);
        analysisGoal.addFormula(new SequentFormula(fact), false, true);
    }

    /**
     * TODO
     * 
     * @param pio
     * @param analysisGoal
     * @param fact
     */
    public static void prepareGoal(final PosInOccurrence pio,
            final Goal analysisGoal, final Term fact) {
        prepareGoal(pio, analysisGoal, fact, "Covers fact");
    }

    /**
     * TODO
     * 
     * @param analysisGoal
     * @param firstLabel
     */
    public static OriginOfFormula findOriginOfTermLabel(final Goal analysisGoal,
            final TermLabel firstLabel) {
        Node currNode = analysisGoal.node();
        SequentFormula originForm = null;

        while (!currNode.root()) {
            ImmutableList<TermLabel> allLabelsInNode = ImmutableSLList
                    .<TermLabel> nil();
            final Node parent = currNode.parent();
            for (SequentFormula oSf : parent.sequent()) {
                final Set<TermLabel> labelsInSeqFor = //
                        extractLabelsOfTerm(oSf.formula());

                allLabelsInNode = allLabelsInNode.prepend(labelsInSeqFor);
                if (labelsInSeqFor.contains(firstLabel)) {
                    originForm = oSf;
                    break;
                }
            }

            if (!allLabelsInNode.contains(firstLabel)) {
                break;
            } else {
                currNode = parent;
            }
        }

        return new OriginOfFormula(currNode, originForm);
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    public static Set<TermLabel> extractLabelsOfTerm(Term t) {
        final Set<TermLabel> labelsInSeqFor = new LinkedHashSet<TermLabel>();
        t.execPreOrder(new DefaultVisitor() {
            @Override
            public void visit(Term visited) {
                if (visited.hasLabels()) {
                    labelsInSeqFor.addAll(StreamSupport
                            .stream(visited.getLabels().spliterator(), true)
                            .collect(Collectors.toList()));
                }
            }
        });
        return labelsInSeqFor;
    }

    /**
     * TODO
     * 
     * @param node
     * @return
     */
    public static List<Node> extractOpenNodesWithModality(Node node) {
        return GeneralUtilities.toStream(node.proof().getSubtreeGoals(node))
                .map(g -> g.node())
                .filter(n -> GeneralUtilities.toStream(n.sequent().succedent())
                        .anyMatch(
                                f -> f.formula().containsJavaBlockRecursive()))
                .collect(Collectors.toList());
    }

    /**
     * TODO
     * 
     * @param analysisGoal
     */
    public static void removeLoopInvFormulasFromAntec(final Goal analysisGoal) {
        for (SequentFormula sf : analysisGoal.sequent().antecedent()) {
            final ImmutableArray<TermLabel> labels = sf.formula().getLabels();
            if (labels.size() > 0) {
                final TermLabel firstLabel = labels.get(0);

                // Find origin of this label
                final OriginOfFormula origin = //
                        findOriginOfTermLabel(analysisGoal, firstLabel);

                if (origin.getNode().parent()
                        .getAppliedRuleApp() instanceof LoopInvariantBuiltInRuleApp) {
                    // This has to be the anonymized invariant (or part of
                    // it) -- remove it
                    analysisGoal.removeFormula(new PosInOccurrence(sf,
                            PosInTerm.getTopLevel(), true));
                }
            }
        }
    }

    /**
     * TODO
     * 
     * @param tb
     * @param goal
     */
    public static void addSETPredicateToAntec(final Goal goal) {
        final Optional<Pair<SequentFormula, Term>> maybeSETPredicate = //
                GeneralUtilities.toStream(goal.sequent().succedent())
                        .map(sf -> {
                            SETPredVisitor v = new SETPredVisitor();
                            sf.formula().execPostOrder(v);
                            return new Pair<SequentFormula, Term>(sf,
                                    v.getSetPredTerm());
                        }).filter(p -> p.second != null).findAny();

        if (!maybeSETPredicate.isPresent()) {
            // There are easy goals where the post condition is just "false", so
            // that should be OK
            return;
        }

        Term newFormula = maybeSETPredicate.get().second;
        final Term seqFor = maybeSETPredicate.get().first.formula();
        if (seqFor.op() instanceof UpdateApplication) {
            newFormula = goal.proof().getServices().getTermBuilder()
                    .apply(seqFor.sub(0), newFormula);
            assert !(seqFor.sub(1).op() instanceof UpdateApplication);
        }

        goal.addFormula(new SequentFormula(newFormula), true, false);
    }

    /**
     * TODO
     *
     * @author Dominic Steinhöfel
     */
    public static class OriginOfFormula {
        private final Node node;
        private final SequentFormula seqFor;

        public OriginOfFormula(Node node, SequentFormula seqFor) {
            this.node = node;
            this.seqFor = seqFor;
        }

        public Node getNode() {
            return node;
        }

        public SequentFormula getSeqFor() {
            return seqFor;
        }
    }

    public static class SETPredVisitor extends DefaultVisitor {
        private static final String SET_ACCUMULATE = AbstractOperationPO.UNINTERPRETED_PREDICATE_NAME;
        private Term setPredTerm = null;

        @Override
        public void visit(Term visited) {
            if (visited.op().name().toString().equals(SET_ACCUMULATE)) {
                setPredTerm = visited;
            }
        }

        public Term getSetPredTerm() {
            return setPredTerm;
        }
    }

}
