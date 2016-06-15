package de.uka.ilkd.key.rule.join;

import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Rule application class for close-after-join rule applications.
 * 
 * @author Dominic Scheurer
 */
public class CloseAfterJoinRuleBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private Node partnerNode, correspondingJoinNode;

    private SymbolicExecutionState joinNodeState = null;
    private SymbolicExecutionState partnerState = null;
    private JavaDLTerm pc = null;

    public CloseAfterJoinRuleBuiltInRuleApp(BuiltInRule builtInRule,
            PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pio, Node thePartnerNode,
            Node correspondingJoinNode, SymbolicExecutionState joinNodeState,
            SymbolicExecutionState partnerState, JavaDLTerm pc) {
        this(builtInRule, pio);
        setThePartnerNode(thePartnerNode);
        setCorrespondingJoinNode(correspondingJoinNode);
        setJoinNodeState(joinNodeState);
        setPartnerState(partnerState);
        setPc(pc);
    }

    public CloseAfterJoinRuleBuiltInRuleApp(BuiltInRule builtInRule,
            PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pio) {
        super(builtInRule, pio);
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> newPos) {
        return null;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        return this;
    }

    @Override
    public boolean complete() {
        return partnerNode != null && correspondingJoinNode != null
                && joinNodeState != null && partnerState != null && pc != null;
    }

    // // GETTERS AND SETTERS // //

    public Node getThePartnerNode() {
        return partnerNode;
    }

    public void setThePartnerNode(Node thePartnerNode) {
        this.partnerNode = thePartnerNode;
    }

    public Node getCorrespondingJoinNode() {
        return correspondingJoinNode;
    }

    public void setCorrespondingJoinNode(Node correspondingJoinNode) {
        this.correspondingJoinNode = correspondingJoinNode;
    }

    public SymbolicExecutionState getJoinState() {
        return joinNodeState;
    }

    public void setJoinNodeState(SymbolicExecutionState joinState) {
        this.joinNodeState = joinState;
    }

    public SymbolicExecutionState getPartnerSEState() {
        return partnerState;
    }

    public void setPartnerState(SymbolicExecutionState thisSEState) {
        this.partnerState = thisSEState;
    }

    public JavaDLTerm getPc() {
        return pc;
    }

    public void setPc(JavaDLTerm pc) {
        this.pc = pc;
    }

}
