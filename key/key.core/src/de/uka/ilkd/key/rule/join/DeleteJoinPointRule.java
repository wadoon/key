package de.uka.ilkd.key.rule.join;

import java.util.HashMap;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

public class DeleteJoinPointRule implements BuiltInRule {

    public static final DeleteJoinPointRule INSTANCE = new DeleteJoinPointRule();

    private static final String DISPLAY_NAME = "DeleteJoinPoint";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public DeleteJoinPointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {

        ImmutableList<Goal> goals = goal.split(1);
        goal = goals.head();
        Term target =  TermBuilder.goBelowUpdates(ruleApp.posInOccurrence().subTerm());
        JavaBlock newJavaBlock = JavaTools.removeActiveStatement(target.javaBlock(), services);
        TermBuilder tb = services.getTermBuilder();
        Term newFormula = tb.prog((Modality)target.op(), newJavaBlock,
                target.sub(0));
        goal.changeFormula(
                new SequentFormula(tb.apply(
                        UpdateApplication.getUpdate(ruleApp.posInOccurrence().subTerm()), newFormula)),
                ruleApp.posInOccurrence());
        return goals;
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

        if (pio != null && JavaTools.getActiveStatement(TermBuilder.goBelowUpdates(pio.subTerm())
                        .javaBlock()) instanceof JoinPointStatement
        /*
         * JoinPointRule.isJoinPointStatement(JoinRuleUtils
         * .getJavaBlockRecursive(pio.subTerm()).program()) != null
         */) {

            ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                    .findPotentialJoinPartners(goal, pio);

            if (joinPartners.isEmpty() && goal.appliedRuleApps()
                    .head() instanceof JoinRuleBuiltInRuleApp) {
                return true;
                /*
                 * for (RuleApp rA : goal.appliedRuleApps()) { if (rA instanceof
                 * JoinRuleBuiltInRuleApp) return true; }
                 */
            }

        }
        return false;

    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new DeleteJoinPointBuiltInRuleApp(this, pos);
    }

    
    }

 
