package de.uka.ilkd.key.proof.runallproofs.performance;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.runallproofs.StatisticsGathering;

public class NodeData {

    final Map<String, RuleData> ruleName2RuleData = new HashMap<>();
    final int id;
    final int proofTreeDepth;
    final int astDepth;

    private static int getDepth(Node node) {
        int depth = -1;
        while (node != null) {
            node = node.parent();
            depth++;
        }
        return depth;
    }

    NodeData(Goal goal) {
        Node node = goal.node();
        id = node.serialNr();
        proofTreeDepth = getDepth(node);
        astDepth = StatisticsGathering.countAST(node);
    }
}
