package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.*;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 * This rule can be used to close a goal by reference to an already closed node. The referred node
 * must have exactly the same sequent as the goal where the rule shall be applied to. Furthermore,
 * both nodes must have the same partially instantiated NoPosTacletApps (e.g., insert_hidden_
 * rules) for the goal to be closable.
 *
 * @author Wolfram Pfeifer
 */
public final class CloseByReferenceRule implements BuiltInRule {
    /** the only instance of this rule */
    public static final CloseByReferenceRule INSTANCE = new CloseByReferenceRule();

    /** the display name as a string */
    private static final String DISPLAY_NAME = "CloseByReferenceRule";

    /** the name of this rule */
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    private CloseByReferenceRule() {
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // can only be applied on the sequent arrow, i.e., to the goal itself
        return pio == null;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new CloseByReferenceRuleApp(this, pos);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
        throws RuleAbortException {

        CloseByReferenceRuleApp app = (CloseByReferenceRuleApp) ruleApp;
        PosInOccurrence pio = app.posInOccurrence();

        assert pio == null;

        if (!app.complete()) {
            return null;
        }

        Node currentNode = goal.node();
        Node partnerNode = app.getPartner();

        // TODO: currently, the partner has to be closed (could probably be relaxed) ...
        if (!partnerNode.isClosed()) {
            return null;
        }

        // goal must have the same sequent as its partner node (strategy irrelevant term labels and
        // order of formulas are ignored)
        // TODO: we have to use a special equals method chain, since we want LogicVariables with
        //  same name and sort to be equal
        if (!equalModTermLabels(goal.sequent(), partnerNode.sequent())) {
        //if (!goal.sequent().equalsModIrrelevantTermLabels(partnerNode.sequent())) {
            return null;
        }

        // Ensures that both nodes have the same partially instantiated NoPosTaclets (in particular
        // insert_hidden_ rules). Otherwise, it would be a soundness problem.
        if (!localRulesAreCompatible(goal, partnerNode)) {
            return null;
        }

        final ImmutableList<Goal> result = goal.split(1);
        final Goal resultGoal = result.head();

        /* for saving/loading we ensure that the partner has a unique persistent serial number,
         * however, in the GUI we show the non-persistent serialNr */
        partnerNode.getNodeInfo().requestPersistentNodeId();
        resultGoal.setBranchLabel("Closed by reference to node " + partnerNode.serialNr());

        Proof proof = goal.proof();
        proof.addProofTreeListener(new ProofTreeAdapter() {
            @Override
            public void proofPruned(ProofTreeEvent e) {
                // this additional check is necessary, because the partner node could have already
                // been removed by the pruning operation
                if (proof.find(partnerNode)) {
                    if (!partnerNode.isClosed()) {
                        // partnerNode was reopened by pruning -> reopen currentNode (deletes
                        // the CloseByReferenceRule application)
                        proof.pruneProof(currentNode);

                        // the listener is not needed anymore
                        proof.removeProofTreeListener(this);
                    }
                }
                // TODO: some listeners may be invalid and still present ...
            }
        });

        return resultGoal.split(0);
    }

    public static boolean equalModTermLabels(Sequent s1, Sequent s2) {
        return equalModTermLabels(s1.antecedent(), s2.antecedent())
            && equalModTermLabels(s1.succedent(), s2.succedent());
    }

    public static boolean equalModTermLabels(Semisequent s1, Semisequent s2) {
        if (s1.asList().size() != s2.asList().size()) {
            return false;
        }
        for (SequentFormula sf1 : s1.asList()) {
            boolean found = false;
            for (SequentFormula sf2 : s2.asList()) {
                if (equalModTermLabels(sf1.formula(), sf2.formula())) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
        }
        return true;
    }

    public static boolean equalModTermLabels(Term t1, Term t2) {
        // currently, TermImpl is the only class implementing Term interface
        // TODO: a simple string comparison could also work here ...
        return equalsModIrrelevantTermLabels((TermImpl) t1, (TermImpl) t2);
    }

    public static boolean equalsModIrrelevantTermLabels(TermImpl t1, TermImpl t2) {
        if(t1 == t2) {
            return true;
        }

        if(t1 == null || t2 == null) {
            return false;
        }

        if (!(equalOp(t1.op(), t2.op())
            && equalBoundVariables(t1, t2)
            && t1.javaBlock().equals(t2.javaBlock()))) {
            return false;
        }

        for (TermLabel label : t1.getLabels()) {
            if (label.isProofRelevant() && !t2.getLabels().contains(label)) {
                return false;
            }
        }

        for (TermLabel label : t2.getLabels()) {
            if (label.isProofRelevant() && !t1.getLabels().contains(label)) {
                return false;
            }
        }

        for (int i = 0; i < t1.subs().size(); ++i) {
            if (!equalModTermLabels(t1.sub(i), t2.sub(i))) {
            //if (!t1.sub(i).equalsModIrrelevantTermLabels(t2.sub(i))) {
                return false;
            }
        }

        return true;
    }

    private static boolean equalOp(Operator op1, Operator op2) {
        if (op1 instanceof LogicVariable && op2 instanceof LogicVariable) {
            return equalsLogicVar((LogicVariable) op1, (LogicVariable) op2);
        } else {
            return op1.equals(op2);
        }
    }

    private static boolean equalBoundVariables(TermImpl t1, TermImpl t2) {
        ImmutableArray<QuantifiableVariable> vars1 = t1.boundVars();
        ImmutableArray<QuantifiableVariable> vars2 = t2.boundVars();

        if (vars1 == vars2) {
            return true;
        }

        if (vars1 == null || vars2 == null || vars1.size() != vars2.size()) {
            return false;
        }

        for (int i = 0; i < vars1.size(); i++) {
            QuantifiableVariable qv1 = vars1.get(i);
            QuantifiableVariable qv2 = vars2.get(i);
            if (qv1 instanceof LogicVariable && qv2 instanceof LogicVariable) {
                // only compare name and sort for LogicVariables
                if (!equalsLogicVar((LogicVariable) qv1, (LogicVariable) qv2)) {
                    return false;
                }
            } else {
                // needed to correctly compare VariableSV
                if (!qv1.equals(qv2)) {
                    return false;
                }
            }
        }
        return true;
    }

    private static boolean equalsLogicVar(LogicVariable lv1, LogicVariable lv2) {
        return lv1.name().equals(lv2.name()) && lv1.sort().equals(lv2.sort());
    }

    /**
     * Checks if the local rules (e.g., insert_hidden rules) of the goal are compatible to those
     * available at the node. Compatible means that each rule available at partnerNode must also
     * be available at currentGoal, however, currentGoal may have additional local rules.
     * @param currentGoal the goal which shall be closed by reference
     * @param partnerNode the potential reference partner which could be used to close the goal
     * @return true iff the rules are compatible
     */
    public static boolean localRulesAreCompatible(Goal currentGoal, Node partnerNode) {
        // collect all locally introduced rules that could differ between current and partner node
        Node currentNode = currentGoal.node();
        Node commonAncestor = currentNode.commonAncestor(partnerNode);
        Set<NoPosTacletApp> localTaclets = new HashSet<>();
        Node n = partnerNode;
        while (n != commonAncestor) {
            for (NoPosTacletApp localApp : n.getLocalIntroducedRules()) {
                localTaclets.add(localApp);
            }
            n = n.parent();
        }

        // closing by reference is only allowed if the referenced node does not have hidden rules
        // which are not present in the goal to close. Otherwise it would be a soundness problem.
        for (NoPosTacletApp localApp : localTaclets) {
            // this is probably slow, but should be ok since localTaclets is of small size ...
            if (!currentGoal.indexOfTaclets().getPartialInstantiatedApps().contains(localApp)) {

                // we check if the insert taclet is used: if not, closing is still sound
                for (Iterator<Node> it = partnerNode.subtreeIterator(); it.hasNext(); ) {
                    Node node = it.next();
                    if (node.getAppliedRuleApp() == localApp) {
                        // localApp is used somewhere -> not applicable
                        return false;
                    }
                }
                // found at least one different -> not applicable
                //return false;
            }
        }
        return true;
    }

    @Override
    public Name name() {
        return RULE_NAME;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public String toString() {
        return displayName();
    }

    /**
     * Rule application class for closing by reference. Is complete iff the partner node which
     * the goal should refer to has been set (by using the setter method).
     *
     * @author Wolfram Pfeifer
     */
    public static final class CloseByReferenceRuleApp extends AbstractBuiltInRuleApp {
        /** The partner the goal refers to. Must be closed already. */
        private Node partner;

        private CloseByReferenceRuleApp(BuiltInRule rule, PosInOccurrence pio) {
            super(rule, pio);
        }

        @Override
        public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
            return this;
        }

        @Override
        public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
            return this;
        }

        @Override
        public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
            return this;
        }

        @Override
        public boolean complete() {
            return partner != null;
        }

        @Override
        public String toString() {
            return "BuiltInRule: " + rule().name();
        }

        public Node getPartner() {
            return partner;
        }

        public void setPartner(Node partner) {
            this.partner = partner;
        }
    }
}
