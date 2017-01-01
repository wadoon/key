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
                && isJoinPointStatement(JoinRuleUtils
                        .getJavaBlockRecursive(pio.subTerm()).program())) {
           
            ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                    .findPotentialJoinPartners(goal, pio);
            
            if (!joinPartners.equals(ImmutableSLList.nil())) {
                return true;
            }
        }
        
        return false;

    }

    public static boolean isJoinPointStatement(ProgramElement pE) {

        if (pE != null && pE instanceof StatementBlock
                && ((StatementBlock) pE).getInnerMostMethodFrame() != null
                && ((StatementBlock) pE).getInnerMostMethodFrame().getBody() != null
                && ((StatementBlock) pE).getInnerMostMethodFrame().getBody()
                        .getFirstElement() instanceof JoinPointStatement)
            return true;

        else
            return false;

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
