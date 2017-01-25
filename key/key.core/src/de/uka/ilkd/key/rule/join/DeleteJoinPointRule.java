package de.uka.ilkd.key.rule.join;

import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;

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

        if (pio == null || !pio.subTerm().isContainsJavaBlockRecursive()) {
            return false;
        }

        SourceElement activeStatement = JavaTools.getActiveStatement(
                TermBuilder.goBelowUpdates(pio.subTerm()).javaBlock());

        if (!(activeStatement instanceof JoinPointStatement)) {
            return false;
        }

        JoinPointStatement jps = ((JoinPointStatement) activeStatement);

        boolean result = StreamSupport
                .stream(goal.proof().openGoals().spliterator(), true)
                .filter(g -> g != goal && !g.isLinked())
                .filter(g -> JoinPointRule.containsJPS(g, jps))
                .collect(Collectors.counting()).intValue() == 0;
        return result;
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
