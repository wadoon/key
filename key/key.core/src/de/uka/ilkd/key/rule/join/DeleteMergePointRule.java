package de.uka.ilkd.key.rule.join;

import org.key_project.util.collection.ImmutableList;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;

public class DeleteMergePointRule implements BuiltInRule {

    public static final DeleteMergePointRule INSTANCE = new DeleteMergePointRule();

    private static final String DISPLAY_NAME = "DeleteJoinPoint";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public DeleteMergePointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {

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
            && JavaTools
                .getActiveStatement(TermBuilder.goBelowUpdates(pio.subTerm())
                        .javaBlock()) instanceof MergePointStatement) {

            MergePointStatement mps = (MergePointStatement) JavaTools
                    .getActiveStatement(TermBuilder
                            .goBelowUpdates(pio.subTerm()).javaBlock());
            for (Goal g : goal.proof().openGoals()) {
                if (!g.equals(goal) && !g.isLinked() && MergePointRule
                        .containsMergePoint(g, mps, goal.proof().getServices())){
                    return false;
                }
            }
            return true;

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
        return new DeleteMergePointBuiltInRuleApp(this, pos);
    }

}
