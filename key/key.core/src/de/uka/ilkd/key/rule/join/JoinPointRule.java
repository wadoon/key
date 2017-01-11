package de.uka.ilkd.key.rule.join;

import java.util.HashMap;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.intermediate.BuiltInAppIntermediate;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.SimpleBlockContract;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

public class JoinPointRule implements BuiltInRule {
    public static final JoinPointRule INSTANCE = new JoinPointRule();

    private static final String DISPLAY_NAME = "Join Point";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public JoinPointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {

        PosInOccurrence pio = ruleApp.posInOccurrence();
        JoinRuleBuiltInRuleApp app = new JoinRuleBuiltInRuleApp(new JoinRule(),
                pio);

        StatementBlock block = (StatementBlock) JoinRuleUtils
                .getJavaBlockRecursive(pio.subTerm()).program();

        JoinProcedure concreteRule = ((JoinPointStatement) block
                .getInnerMostMethodFrame().getBody().getFirstElement())
                        .getJoinProc();

        ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                .findPotentialJoinPartners(goal, pio, goal.proof().root());

        app.setJoinNode(goal.node());
        app.setConcreteRule(concreteRule);
        app.setJoinPartners(joinPartners);

        ImmutableList<Goal> newGoals = goal.split(1);
        Goal g = newGoals.head();
        newGoals = g.apply(app);

        return newGoals;
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

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {

        if (pio != null && pio.subTerm().isContainsJavaBlockRecursive()
                && !goal.isLinked()) {

            SourceElement st = JavaTools.getActiveStatement(
                    TermBuilder.goBelowUpdates(pio.subTerm()).javaBlock());

            if (st instanceof JoinPointStatement) {

                BlockContract contract = ((JoinPointStatement) st)
                        .getContract();

                ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                        .findPotentialJoinPartners(goal, pio);

                if (!joinPartners.isEmpty()) {

                    ImmutableList<Goal> joinPartnersGoal = ImmutableSLList
                            .nil();

                    for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> p : joinPartners) {
                        joinPartnersGoal = joinPartnersGoal.append(p.first);
                    }

                    ImmutableList<Goal> openGoals = goal.node().proof()
                            .openGoals();
                    for (Goal g : openGoals) {
                        // not linked
                        if (!g.equals(goal) && !g.isLinked()
                                && !joinPartnersGoal.contains(g)) {

                            if (hasSameBlockContractRule(g, contract))
                                return false;

                            JavaBlock jB;
                            for (int i = 0; i < g.node().sequent().succedent()
                                    .size(); i++) {
                                jB = JoinRuleUtils.getJavaBlockRecursive(
                                        g.node().sequent().succedent().get(i)
                                                .formula());
                                MethodFrame mF = JavaTools
                                        .getInnermostMethodFrame(jB,
                                                goal.proof().getServices());
                                if (mF != null && hasSameBlock(mF.getBody(),
                                        contract.getBlock())) {

                                    return false;
                                }
                            }

                        }
                    }
                    return true;
                }
            }
        }

        return false;
    }

    private boolean hasSameBlockContractRule(Goal g, BlockContract contract) {
        for (RuleApp rA : g.appliedRuleApps()) {
            if (rA instanceof BlockContractBuiltInRuleApp
                    && ((BlockContractBuiltInRuleApp) rA).getContract()
                            .equals(contract))
                return true;
        }
        return false;
    }

    // TODO: test more complex cases
    private boolean hasSameBlock(StatementBlock block1, StatementBlock block2) {
        boolean result = false;
        ProgramElement pE;
        for (int i = 0; i < block1.getChildCount() && !result; i++) {
            pE = block1.getChildAt(i);
           result = (pE instanceof StatementBlock) ? (pE.equals(block2)) ? true :  hasSameBlock((StatementBlock) pE,
                            block2): false;
                }
        return result;
        }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new JoinPointBuiltInRuleApp(this, pos);
    }

}
