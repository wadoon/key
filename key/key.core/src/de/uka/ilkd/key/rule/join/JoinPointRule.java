package de.uka.ilkd.key.rule.join;

import java.util.HashMap;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
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

        if (pio != null && pio.subTerm().isContainsJavaBlockRecursive()) {
            BlockContract contract = isJoinPointStatement(JoinRuleUtils
                    .getJavaBlockRecursive(pio.subTerm()).program());

            if (contract != null) {
                ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                        .findPotentialJoinPartners(goal, pio);
                ImmutableList<Goal> joinPartnersGoal = ImmutableSLList.nil();

                for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> p : joinPartners) {
                    joinPartnersGoal = joinPartnersGoal.append(p.first);
                }

                if (!joinPartners.isEmpty()) {
                    ImmutableList<Goal> openGoals = goal.node().proof()
                            .openGoals();
                    for (Goal g : openGoals) {
                        //not linked
                        if (!g.equals(goal) && !g.isLinked() && !joinPartnersGoal.contains(g)) {
                            JavaBlock jB;
                            for(int i = 0; i < g.node().sequent().succedent().size(); i++){
                            jB = JoinRuleUtils
                                    .getJavaBlockRecursive(g.node().sequent()
                                            .succedent().get(i).formula());
                            jB.isEmpty();

                            if (((StatementBlock) jB.program())
                                    .getInnerMostMethodFrame() != null && hasSameBlock(((StatementBlock) jB.program())
                                    .getInnerMostMethodFrame().getBody(),
                                    contract.getBlock())) {

                                return false;
                            }
                            }
                            if (hasSameBlockContractRule(g, contract))
                                return false;
                        }
                    }
                    return true;
                }
            }
        }

        return false;
    }

    private boolean hasSameBlockContractRule(Goal g,
            BlockContract contract) {
        for (RuleApp rA : g.appliedRuleApps()) {
            if (rA instanceof BlockContractBuiltInRuleApp
                    && ((BlockContractBuiltInRuleApp) rA).getContract()
                            .equals(contract))
                return true;
        }
        return false;
    }

    private boolean hasSameBlock(StatementBlock block1, StatementBlock block2) {

        for (int i = 0; i < block1.getChildCount(); i++) {
            if (block1.getChildAt(i) != null
                    && block1.getChildAt(i) instanceof StatementBlock) {
                if (block1.getChildAt(i).equals(block2)) {
                    return true;
                }
                else {
                    return hasSameBlock((StatementBlock) block1.getChildAt(0),
                            block2);
                }
            }
        }
        return false;
    }

    public static BlockContract isJoinPointStatement(ProgramElement pE) {

        if (pE != null && pE instanceof StatementBlock
                && ((StatementBlock) pE).getInnerMostMethodFrame() != null
                && ((StatementBlock) pE).getInnerMostMethodFrame()
                        .getBody() != null){
            SourceElement st = ((StatementBlock) pE).getInnerMostMethodFrame().getBody()
            .getFirstElement();
            if(st instanceof JoinPointStatement){
                return ((JoinPointStatement) st)
                                .getContract();
            }
            
        }
        return null;

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
