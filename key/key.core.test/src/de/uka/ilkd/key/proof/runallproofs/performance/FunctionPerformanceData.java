package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class FunctionPerformanceData {

    private final Map<Integer, NodeData> nodeId2NodeData = new HashMap<>();
    private final File dataDir;
    private final DataRecordingTestFile dataRecordingTestFile;
    
    public int totalInvocations = 0;
    public long totalDuration = 0;

    public FunctionPerformanceData(File dataDir, DataRecordingTestFile dataRecordingTestFile) {
        this.dataRecordingTestFile = dataRecordingTestFile;
        this.dataDir = dataDir;
    }

    private NodeData getDataMapForGoal(Goal goal) {
        NodeData nodeData = nodeId2NodeData.get(goal.node().serialNr());
        if (nodeData == null) {
            nodeData = new NodeData(goal);
            nodeId2NodeData.put(nodeData.id, nodeData);
        }
        return nodeData;
    }

    public void addDurationToData(RuleApp app, Goal goal, long duration) {
        NodeData map = getDataMapForGoal(goal);
        String ruleName = app.rule().displayName();
        RuleData ruleData = map.ruleName2RuleData.get(ruleName);
        if (ruleData == null) {
            ruleData = new RuleData(duration);
            map.ruleName2RuleData.put(ruleName, ruleData);
        } else {
            ruleData.addDuration(duration);
        }
        
        totalInvocations++;
        totalDuration += duration;
    }

    private PrintWriter getWriter(String ruleName, Map<String, PrintWriter> writers) {
        PrintWriter writer = writers.get(ruleName);
        if (writer == null) {
            try {
                writer = new PrintWriter(new FileOutputStream(new File(dataDir, ruleName + ".data"),
                        true /* append = true */));
                writers.put(ruleName, writer);
                writer.append("# " + dataRecordingTestFile.getKeYFile().getName() + "\n");
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
            writer.append("# nodeId astCount proofTreeDepth computCostInvocations computeCostDuration ccAvg\n");
        }
        return writer;
    }

    public void updateData() {
        Map<String, PrintWriter> writers = new HashMap<>();
        Collection<NodeData> nodeData = nodeId2NodeData.values();
        for (NodeData node : nodeData) {
            for (Entry<String, RuleData> entry : node.ruleName2RuleData.entrySet()) {
                StringBuffer sb = new StringBuffer();
                sb.append(node.id + " ");
                sb.append(node.astDepth + " ");
                sb.append(node.proofTreeDepth + " ");
                RuleData ruleData = entry.getValue();
                int ccInvoc = ruleData.numberInvocationsForRule;
                long ccDur = ruleData.totalRuleTime;
                sb.append(ccInvoc + " ");
                sb.append(ccDur + " ");
                sb.append(((double) ccDur) / ((double) ccInvoc) + "\n");
                getWriter(entry.getKey(), writers).append(sb.toString());
            }
        }
        for (PrintWriter writer : writers.values()) {
            writer.close();
        }
    }

}
