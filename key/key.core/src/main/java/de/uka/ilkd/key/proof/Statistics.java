package de.uka.ilkd.key.proof;

import java.util.*;

import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.SideProofStatistics;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.OneStepSimplifier.Protocol;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.util.EnhancedStringBuffer;
import de.uka.ilkd.key.util.Pair;

/**
 * Instances of this class encapsulate statistical information about proofs,
 * such as the number of nodes, or the number of interactions.
 * @author bruns
 *
 */
public class Statistics {
    public final int nodes;
    public final int branches;
    public final int interactiveSteps;
    public final int symbExApps;
    public final int quantifierInstantiations;
    public final int heur_call;
    public final long heur_ms;
    public final int bg_norm_calls;
    public final int bg_norm_execs;
    public final int normRuleApps;
    public final int ossApps;
    public final int mergeRuleApps;
    public final int totalRuleApps;
    public final int smtSolverApps;
    public final int dependencyContractApps;
    public final int operationContractApps;
    public final int blockLoopContractApps;
    public final int loopInvApps;
    public final long normTimeInMillis;
    public final long autoModeTimeInMillis;
    public final long timeInMillis;
    public final float timePerStepInMillis;




    private List<Pair<String, String>> summaryList =
                    new ArrayList<Pair<String, String>>(14);

    private final HashMap<String, Integer> interactiveAppsDetails =
            new HashMap<String, Integer>();

    protected Statistics(int nodes,
                         int branches,
                         int interactiveSteps,
                         int symbExApps,
                         int quantifierInstantiations,
                         int heur_call,
                         long heur_ms,
                         int bg_norm_calls,
                         int bg_norm_execs,
                         int normRuleApps,
                         int ossApps,
                         int mergeRuleApps,
                         int totalRuleApps,
                         int smtSolverApps,
                         int dependencyContractApps,
                         int operationContractApps,
                         int blockLoopContractApps,
                         int loopInvApps,
                         long normTimeInMillis,
                         long autoModeTimeInMillis,
                         long timeInMillis,
                         float timePerStepInMillis) {
        this.nodes = nodes;
        this.branches = branches;
        this.interactiveSteps = interactiveSteps;
        this.symbExApps = symbExApps;
        this.quantifierInstantiations = quantifierInstantiations;
        this.heur_call = heur_call;
        this.heur_ms = heur_ms;
        this.bg_norm_calls = bg_norm_calls;
        this.bg_norm_execs = bg_norm_execs;
        this.normRuleApps = normRuleApps;
        this.ossApps = ossApps;
        this.mergeRuleApps = mergeRuleApps;
        this.totalRuleApps = totalRuleApps;
        this.smtSolverApps = smtSolverApps;
        this.dependencyContractApps = dependencyContractApps;
        this.operationContractApps = operationContractApps;
        this.blockLoopContractApps = blockLoopContractApps;
        this.loopInvApps = loopInvApps;
        this.normTimeInMillis = normTimeInMillis;
        this.autoModeTimeInMillis = autoModeTimeInMillis;
        this.timeInMillis = timeInMillis;
        this.timePerStepInMillis = timePerStepInMillis;
    }

    Statistics(Node startNode) {
        final Iterator<Node> it = startNode.subtreeIterator();

        TemporaryStatistics tmp = new TemporaryStatistics();

        Node node;
        while (it.hasNext()) {
            node = it.next();
            tmp.changeOnNode(node, interactiveAppsDetails);
        }

        this.nodes = tmp.nodes;
        this.branches = tmp.branches;
        this.interactiveSteps = tmp.interactive;
        this.symbExApps = tmp.symbExApps;
        this.quantifierInstantiations = tmp.quant;
        this.heur_call = tmp.heur_call;
        this.heur_ms = tmp.heur_ms;
        this.ossApps = tmp.oss;
        this.mergeRuleApps = tmp.mergeApps;
        this.normRuleApps = tmp.norm;
        this.totalRuleApps = tmp.nodes + tmp.ossCaptured - 1;
        this.smtSolverApps = tmp.smt;
        this.dependencyContractApps = tmp.dep;
        this.operationContractApps = tmp.contr;
        this.blockLoopContractApps = tmp.block;
        this.loopInvApps = tmp.inv;
        this.bg_norm_calls = tmp.bg_norm_calls;
        this.bg_norm_execs = tmp.bg_norm_execs;
        this.normTimeInMillis = tmp.bg_norm_exec_ms;
        this.autoModeTimeInMillis = startNode.proof().getAutoModeTime();
        this.timeInMillis = (System.currentTimeMillis() - startNode.proof().creationTime);
        timePerStepInMillis = nodes <= 1 ? .0f : (autoModeTimeInMillis / (float)(nodes - 1));

        generateSummary(startNode.proof());
    }

    Statistics(Proof proof) {
        this(proof.root());
    }

    static Statistics create(Statistics side, long creationTime) {
        return new Statistics(side.nodes,
                              side.branches,
                              side.interactiveSteps,
                              side.symbExApps,
                              side.quantifierInstantiations,
                              side.heur_call,
                              side.heur_ms,
                              side.bg_norm_calls,
                              side.bg_norm_execs,
                              side.normRuleApps,
                              side.ossApps,
                              side.mergeRuleApps,
                              side.totalRuleApps,
                              side.smtSolverApps,
                              side.dependencyContractApps,
                              side.operationContractApps,
                              side.blockLoopContractApps,
                              side.loopInvApps,
                              side.autoModeTimeInMillis,
                              side.normTimeInMillis,
                              System.currentTimeMillis() - creationTime,
                              side.timePerStepInMillis);
    }

    private void generateSummary(Proof proof) {
        Statistics stat = this;

        boolean sideProofs = false;
        if (proof instanceof InfFlowProof) { // TODO: get rid of that instanceof by subclassing
            sideProofs = ((InfFlowProof) proof).hasSideProofs();
            if (sideProofs) {
                final long autoTime = proof.getAutoModeTime()
                        + ((InfFlowProof)proof).getSideProofStatistics().autoModeTimeInMillis;
                final SideProofStatistics side =
                        ((InfFlowProof) proof).getSideProofStatistics()
                                    .add(this).setAutoModeTime(autoTime);
                stat = Statistics.create(side, proof.creationTime);
            }
        }

        final String nodeString =
                        EnhancedStringBuffer.format(stat.nodes).toString();
        summaryList.add(new Pair<String, String>("Nodes", nodeString));
        summaryList.add(new Pair<String, String>("Branches",
                        EnhancedStringBuffer.format(stat.branches).toString()));
        summaryList.add(new Pair<String, String>("Interactive steps", "" +
                        stat.interactiveSteps));
        summaryList.add(new Pair<String, String>("Symbolic execution steps", "" +
                stat.symbExApps));


        final long time = sideProofs ? stat.autoModeTimeInMillis : proof.getAutoModeTime();

        summaryList.add(new Pair<String, String>("Automode time",
                        EnhancedStringBuffer.formatTime(time).toString()));
        if (time >= 10000L) {
            summaryList.add(new Pair<String, String>("Automode time", time + "ms"));
        }
        summaryList.add(new Pair<String, String>("Normalization Time", stat.normTimeInMillis + "ms"));
        if (stat.nodes > 0) {
            String avgTime = "" + (stat.timePerStepInMillis);
            // round to 3 digits after point
            int i = avgTime.indexOf('.') + 4;
            if (i > avgTime.length()) {
                i = avgTime.length();
            }
            avgTime = avgTime.substring(0, i);
            summaryList.add(new Pair<String, String>("Avg. time per step", "" + avgTime + "ms"));
        }

        summaryList.add(new Pair<String, String>("Rule applications", ""));
        summaryList.add(new Pair<String, String>("Quantifier instantiations",
                                                 "" + stat.quantifierInstantiations));
        summaryList.add(new Pair<String, String>("Norm Calls", "" + stat.bg_norm_calls));
        summaryList.add(new Pair<String, String>("Norm Execs", "" + stat.bg_norm_execs));
        summaryList.add(new Pair<String, String>("Norm Rule Apps", "" + stat.normRuleApps));
        summaryList.add(new Pair<String, String>("One-step Simplifier apps", "" +
                        stat.ossApps));
        summaryList.add(new Pair<String, String>("SMT solver apps", "" +
                        stat.smtSolverApps));
        summaryList.add(new Pair<String, String>("Dependency Contract apps", "" +
                        stat.dependencyContractApps));
        summaryList.add(new Pair<String, String>("Operation Contract apps", "" +
                        stat.operationContractApps));
        summaryList.add(new Pair<String, String>("Block/Loop Contract apps", "" +
                stat.blockLoopContractApps));
        summaryList.add(new Pair<String, String>("Loop invariant apps", "" +
                        stat.loopInvApps));
        summaryList.add(new Pair<String, String>("Merge Rule apps", "" +
                stat.mergeRuleApps));
        summaryList.add(new Pair<String, String>("Total rule apps",
                        EnhancedStringBuffer.format(stat.totalRuleApps).toString()));
    }


    public List<Pair<String, String>> getSummary() {
        return summaryList;
    }

    public HashMap<String, Integer> getInteractiveAppsDetails() {
        return interactiveAppsDetails;
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer("Proof Statistics:\n");
        for (Pair<String, String> p: summaryList) {
            final String c = p.first;
            final String s = p.second;
            sb = sb.append(c);
            if (!"".equals(s)) {
                sb = sb.append(": ").append(s);
            }
            sb = sb.append('\n');
        }
        sb.deleteCharAt(sb.length() - 1);
        return sb.toString();
    }

    private static final HashSet<String> NORMALIZATION_RULE_NAMES = new HashSet<String>() {
        {
            add("nnf_ex2all");
            add("nnf_imp2or");
            // NNF
            add("nnf_notAll");
            add("nnf_notEx");
            add("nnf_notOr");
            add("nnf_notAnd");
            add("nnf_notEqv");
            add("shift_parent_and");
            add("shift_parent_or");
            add("commute_and");
            add("commute_and_2");
            add("commute_or");
            add("commute_or_2");
            add("cnf_rightDist");
            add("cnf_eqv");
            add("ifthenelse_to_or_left");
            add("ifthenelse_to_or_left2");
            add("ifthenelese_to_or_right");
            add("ifthenelse_to_or_right2");
            add("ifthenelse_to_or_for");
            add("ifthenelse_to_or_for2");
            for(int i = 0; i < 5; i++) add("all_pull_out" + i);
            for(int i = 0; i < 5; i++) add("ex_pull_out" + i);



        }
    };

    /**
     * Helper class to add up all rule applications for some nodes
     * @author Michael Kirsten
     */
    private class TemporaryStatistics {
        int nodes = 0; // proof nodes
        int branches = 1; // proof branches
        int interactive = 0; // interactive steps
        int symbExApps = 0; // symbolic execution steps
        int quant = 0; // quantifier instantiations
        int heur_call = 0;
        int heur_ms = 0;
        int norm = 0; // normalization rule applications
        int bg_norm_calls = 0; // background normalization calls
        int bg_norm_execs = 0; // background normalization executes
        int oss = 0; // OSS applications
        int mergeApps = 0; // merge rule applications
        int ossCaptured = 0; // rules apps in OSS protocol
        int smt = 0; // SMT rule apps
        int dep = 0; // dependency contract apps
        int contr = 0; // functional contract apps
        int block = 0; // block and loop contract apps
        int inv = 0; // loop invariants
        int bg_norm_exec_ms = 0; // ms of bg norm execution

        /**
         * Increment numbers of rule applications according to given node
         * and (already collected) interactive rule applications
         * @param node the given node
         * @param interactiveAppsDetails already collected interactive rule applications
         */
        private void changeOnNode(final Node node,
                                  final HashMap<String, Integer> interactiveAppsDetails) {
            nodes++;

            branches += childBranches(node);
            interactive += interactiveRuleApps(node, interactiveAppsDetails);
            symbExApps += NodeInfo.isSymbolicExecutionRuleApplied(node) ? 1 : 0;

            NodeInfo info = node.getNodeInfo();
            bg_norm_calls += info.bg_norm_calls;
            bg_norm_execs += info.bg_norm_execs;
            bg_norm_exec_ms += info.bg_norm_ms;
            heur_call += info.heur_call;
            heur_ms += info.heur_inst_ms;

            final RuleApp ruleApp = node.getAppliedRuleApp();
            if (ruleApp != null) {
                if (ruleApp instanceof de.uka.ilkd.key.rule.OneStepSimplifierRuleApp) {
                    oss++;
                    ossCaptured += tmpOssCaptured(ruleApp);
                } else if (ruleApp instanceof de.uka.ilkd.key.smt.RuleAppSMT) {
                    smt++;
                } else if (ruleApp instanceof UseDependencyContractApp) {
                    dep++;
                } else if (ruleApp instanceof ContractRuleApp) {
                    contr++;
                } else if (ruleApp instanceof AbstractAuxiliaryContractBuiltInRuleApp) {
                    block++;
                } else if (ruleApp instanceof LoopInvariantBuiltInRuleApp) {
                    inv++;
                } else if (ruleApp instanceof MergeRuleBuiltInRuleApp) {
                    mergeApps++;
                } else if (ruleApp instanceof TacletApp) {
                    TacletApp tacApp = (TacletApp) ruleApp;
                    norm += tmpNormalizationRuleApps(tacApp);
                    quant += tmpQuantificationRuleApps(tacApp);
                }
            }
        }

        /**
         * Add the node's children's branches (minus one) to current number of branches
         * @param node the node of which we compute its children's branches
         * @return the children's branches minus one
         */
        private int childBranches(final Node node) {
            final int c = node.childrenCount();
            if (c > 1) {
                return c - 1;
            }
            return 0;
        }

        /**
         * Compute number of interactive rule applications and collect their names.
         * @param node the considered node
         * @param intAppsDetails the already collected interactive rule applications
         * @return the number of interactive rule apllications
         */
        private int interactiveRuleApps(final Node node,
                                        final HashMap<String, Integer>
                                                  intAppsDetails) {
            final int res;
            if (node.getNodeInfo().getInteractiveRuleApplication()) {
                res = 1;
                final String ruleAppName =
                        node.getAppliedRuleApp().rule().name().toString();
                if (!intAppsDetails.containsKey(ruleAppName)) {
                    intAppsDetails.put(ruleAppName, 1);
                } else {
                    intAppsDetails.put(ruleAppName, intAppsDetails.get(ruleAppName) + 1);
                }
            } else {
                res = 0;
            }
            return res;
        }

        /**
         * Compute number of available one-step-simplification rules
         * @param ruleApp the rule application considered
         * @return the number of captured oss rule applications
         */
        private int tmpOssCaptured(final RuleApp ruleApp) {
            int tmpOssCaptured = 0;
            final Protocol protocol =
                    ((de.uka.ilkd.key.rule.OneStepSimplifierRuleApp) ruleApp).getProtocol();
            if (protocol != null) {
                tmpOssCaptured = protocol.size() - 1;
            }
            return tmpOssCaptured;
        }

        /**
         * Compute all rule applications regarding quantifiers
         * @param tacApp the considered rule application
         * @return the number of quantifier rules
         */
        private int tmpQuantificationRuleApps(final TacletApp tacApp) {
            final int res;
            final String tName =
                    tacApp.taclet().name().toString();
            if (tName.startsWith("allLeft")
                    || tName.startsWith("exRight")
                    || tName.startsWith("inst")) {
                res = 1;
            } else {
                res = 0;
            }
            return res;
        }

        /**
         * Compute all rule applications regarding formula normalization steps
         * @param tacApp the considered rule application
         * @return the number of normalization steps
         */
        private int tmpNormalizationRuleApps(final TacletApp tacApp) {
            final String tName = tacApp.taclet().name().toString();
            //tacApp.taclet().ruleSets().forEachRemaining(rule -> rule.n);
            if(NORMALIZATION_RULE_NAMES.contains(tName)) {
                return 1;
            }
            return 0;
        }

    }
}