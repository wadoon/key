package de.uka.ilkd.key.rule.join;

import org.key_project.util.collection.ImmutableList;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;

public class DeleteJoinPointRule implements BuiltInRule {

    public static final DeleteJoinPointRule INSTANCE = new DeleteJoinPointRule();

    private static final String DISPLAY_NAME = "DeleteJoinPoint";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public DeleteJoinPointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {

        // Term formula = ruleApp.posInOccurrence().sequentFormula().formula();
        // Term target = TermBuilder.goBelowUpdates(formula);
        // JavaBlock newJavaBlock =
        // JavaTools.removeActiveStatement(target.javaBlock(), services);
        // TermBuilder tb = services.getTermBuilder();
        // Term newTarget = tb.prog((Modality)target.op(), newJavaBlock,
        // target.sub(0));
        //
        // goal.changeFormula(
        // new SequentFormula(tb.apply(UpdateApplication.getUpdate(formula),
        // newTarget)),
        // ruleApp.posInOccurrence());

        ImmutableList<Goal> goals = goal.split(1);
        goal = goals.head();
        Term target = TermBuilder
                .goBelowUpdates(ruleApp.posInOccurrence().subTerm());
        JavaBlock newJavaBlock = JavaTools
                .removeActiveStatement(target.javaBlock(), services);
        TermBuilder tb = services.getTermBuilder();
        Term newFormula = tb.prog((Modality) target.op(), newJavaBlock,
                target.sub(0));
        goal.changeFormula(
                new SequentFormula(tb.apply(
                        UpdateApplication
                                .getUpdate(ruleApp.posInOccurrence().subTerm()),
                        newFormula)),
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

        if (pio != null
                && JavaTools.getActiveStatement(
                        TermBuilder.goBelowUpdates(pio.subTerm())
                                .javaBlock()) instanceof JoinPointStatement
                && JoinRule.findPotentialJoinPartners(goal, pio).isEmpty()) {
            
            for(Goal g: goal.proof().openGoals()){
                if(!g.equals(goal) && !g.isLinked() && JoinPointRule.containsJPS(g, (JoinPointStatement) JavaTools.getActiveStatement(
                        TermBuilder.goBelowUpdates(pio.subTerm())
                        .javaBlock()))) return false;
            }
            int i = 0;
            ImmutableList<RuleApp> ruleApps = goal.appliedRuleApps();

            while (!ruleApps.isEmpty() && i < 15) {
                if (ruleApps.head() instanceof JoinRuleBuiltInRuleApp) {
                    return true;
                }
                else {
                    ruleApps = ruleApps.tail();
                    i++;
                }
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
