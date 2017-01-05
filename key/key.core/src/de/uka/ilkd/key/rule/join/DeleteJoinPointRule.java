package de.uka.ilkd.key.rule.join;

import java.util.HashMap;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.*;
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
        deleteJoinPointStatement(goal, ruleApp.posInOccurrence(), services);
        return goals;
    }

    @Override
    public Name name() {

        return RULE_NAME;
    }

    @Override
    public String displayName() {
        // TODO Auto-generated method stub
        return DISPLAY_NAME;
    }

    @Override
    public String toString() {
        return displayName();
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {

        if (pio != null && JoinPointRule.isJoinPointStatement(JoinRuleUtils
                .getJavaBlockRecursive(pio.subTerm()).program()) != null) {

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

    private void deleteJoinPointStatement(Goal goal, PosInOccurrence pio,
            Services services) {

        Semisequent succedent = goal.sequent().succedent();
        for (int i = 0; i < succedent.size(); i++) {

            Term formula = succedent.get(i).formula();

            if (!JoinRuleUtils.getJavaBlockRecursive(formula).isEmpty()) {
                StatementBlock oldProgram = (StatementBlock) JoinRuleUtils
                        .getJavaBlockRecursive(formula).program();

                Statement oldTryStatement = oldProgram.getBody().get(0);
                MethodFrame oldMethodFrame = oldProgram
                        .getInnerMostMethodFrame();
                StatementBlock body = oldMethodFrame.getBody();

                // StatementBlock newBody = getBlockWithJPS(body,
                // instantiation.block, services, application);

                int size = body.getBody().toImmutableList().tail().size();
                StatementBlock newInnerBlock = new StatementBlock();
                if (body.getChildAt(0) instanceof StatementBlock) {
                    int size2 = ((StatementBlock) body.getChildAt(0))
                            .getChildCount() - 1;
                    Statement[] array2 = new Statement[size2];
                    StatementBlock newBlock = new StatementBlock(
                            ((StatementBlock) body.getChildAt(0)).getBody()
                                    .toImmutableList().tail().toArray(array2));
                    Statement[] newContent = new Statement[size];
                    newContent[0] = ((Statement) newBlock);
                    for (int k = 1; k < size; k++) {

                        newContent[k] = ((Statement) body.getChildAt(k));
                    }

                    newInnerBlock =  KeYJavaASTFactory.block(newContent);
                }
                else { Statement[] array = new Statement[size];
                // the same as the old inner block but without the
                // JoinPointStatement.
                newInnerBlock = new StatementBlock(
                        body.getBody().toImmutableList().tail().toArray(array));
                }

                MethodFrame newMethodFrame = KeYJavaASTFactory.methodFrame(
                        oldMethodFrame.getProgramVariable(),
                        oldProgram.getInnerMostMethodFrame()
                                .getExecutionContext(),
                        newInnerBlock);

                Statement newProgram = (Statement) new ProgramElementReplacer(
                        oldProgram, services).replace(oldMethodFrame,
                                newMethodFrame);

                JavaBlock newJavaBlock = JavaBlock
                        .createJavaBlock(KeYJavaASTFactory.block(newProgram));

                TermBuilder tb = services.getTermBuilder();
                Term oldTerm = UpdateApplication.getTarget(formula);
                Term newTerm = tb.tf().createTerm(oldTerm.op(), oldTerm.subs(),
                        oldTerm.boundVars(), newJavaBlock);

                goal.changeFormula(
                        new SequentFormula(tb.apply(
                                UpdateApplication.getUpdate(formula), newTerm)),
                        pio);
            }
        }
    }

}
