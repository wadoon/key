package edu.kit.iti.formal.psdbg.interpreter.data;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.StrategyProperties;
import edu.kit.iti.formal.psdbg.LabelFactory;
import lombok.*;

import java.util.HashSet;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @author S. Grebing
 * @version 2 (24.07.17)
 */
@Data
@AllArgsConstructor
@EqualsAndHashCode
@RequiredArgsConstructor
public class KeyData {
    private final KeYEnvironment env;
    private final Proof proof;
    private Node node;

    private String branchingLabel,
            ruleLabel,
            programLinesLabel,
            programStatementsLabel,
            nameLabel;
    private Goal goal;
    private boolean closedNode;

    public KeyData(KeyData data, Goal node) {
        env = data.env;
        //proofApi = data.proofApi;
        //scriptApi = data.scriptApi;
        this.proof = data.proof;
        this.goal = node;
        this.node = goal.node();
        closedNode = this.node.isClosed();

    }

    public KeyData(Goal g, KeYEnvironment environment, Proof proof) {
        goal = g;
        node = goal.node();
        env = environment;
        this.proof = proof;
        //weigl: does not work -> closedNode = proof.closed();
        node = g.node();
    }

    public KeyData(Node root, KeYEnvironment environment, Proof proof) {
        this(proof.getGoal(root), environment, proof);
        node = root;
        closedNode = root.isClosed();
    }

    public KeyData(KeyData kd, Node node) {
        this(node, kd.getEnv(),  kd.getProof());
    }

    /**
     * Return rule name of rule applied to this node
     *
     * @return String representation of applied rule name
     */
    public String getRuleLabel() {
        if (ruleLabel == null) {
            ruleLabel =  LabelFactory.getRuleLabel(getNode());
        }
        return ruleLabel;
    }



    /**
     * Get branching label of node from KeY
     * @return label of this node determining the branching labels in KeY
     */
    public String getBranchingLabel() {
        if (branchingLabel == null) {
            branchingLabel = LabelFactory.getBranchingLabel(getNode());
        }
        return branchingLabel;
    }

    /**
     * Get label with node name from KeY (often applied rulename)
     * @return name of this node
     */
    public String getNameLabel() {
        if (nameLabel == null) {
            nameLabel = LabelFactory.getNameLabel(getNode());
        }
        return nameLabel;
    }

    /**
     * Get lines of active statement
     * @return line of active satetment in original file (-1 if rewritten by KeY or not applicable)
     */
    public String getProgramLinesLabel() {
        if (programLinesLabel == null) {
            programLinesLabel = LabelFactory.getProgramLines(getNode());
        }
        return programLinesLabel;
    }

    /**
     * Get first activestatement for node
     * @return
     */
    public String getProgramStatementsLabel() {
        if (programStatementsLabel == null) {
            programStatementsLabel = LabelFactory.getProgramStatmentLabel(getNode());
        }
        return programStatementsLabel;
    }


    public Goal getGoal() {
        return goal;
    }

    public Node getNode() {
        return node;
        //return getGoal().node();
    }

    public Set<Integer> constructLinesSet() {
        Set<Integer> set = new HashSet<>();

        Node cur = getNode();
        do {

            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                int startPos = activeStatement.getPositionInfo().getStartPosition().getLine();
                int endPos = activeStatement.getPositionInfo().getEndPosition().getLine();
                if (startPos != -1) {
                    if (startPos == endPos) {
                        set.add(startPos);
                    } else {
                        set.add(startPos);
                        set.add(endPos);
                    }
                }
            }
            cur = cur.parent();

        } while (cur != null);
        return set;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("Node with SerNr: ");
        sb.append(this.getNode().serialNr() + " and sequent \n");
        sb.append(this.getNode().sequent() + " and RuleLabels\n");
        sb.append(this.getRuleLabel());
        return sb.toString();
    }


    public StrategyProperties getActiveStrategyProperties() {
        return getProof().getSettings().getStrategySettings().getActiveStrategyProperties();
    }
}
