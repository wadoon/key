package de.uka.ilkd.key.rule.join;

import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.sequentToSETriple;

import java.util.HashMap;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
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
import de.uka.ilkd.key.util.joinrule.ProgramVariablesMatchVisitor;

public class JoinPointRule implements BuiltInRule {
    public static final JoinPointRule INSTANCE = new JoinPointRule();

    private static final String DISPLAY_NAME = "JoinPoint";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public JoinPointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        // delete JoinPointStatement

        PosInOccurrence pio = ruleApp.posInOccurrence();

        JoinRuleBuiltInRuleApp app = new JoinRuleBuiltInRuleApp(new JoinRule(),
                pio);

        JoinProcedure concreteRule = ((JoinPointStatement) ((StatementBlock) JoinRuleUtils
                .getJavaBlockRecursive(pio.subTerm()).program())
                        .getInnerMostMethodFrame().getBody().getFirstElement())
                                .getApplication().getContract()
                                .getJoinProcedure();

        ImmutableList<Goal> joinGoals = getJoinGoals(goal, services);
        ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = getJoinPartners(
                goal, joinGoals, pio, services);

        app.setJoinNode(goal.node());
        app.setConcreteRule(concreteRule);
        app.setJoinPartners(joinPartners);

        ImmutableList<Goal> newGoals = goal.split(1);
        Goal goalB = newGoals.head();
        newGoals = goalB.apply(app);

        ImmutableList<Goal> goals = goal.split(1);
        goal = goals.head();

        if (pio != null && pio.subTerm().isContainsJavaBlockRecursive()
                && JoinRuleUtils.getJavaBlockRecursive(
                        pio.subTerm()) != JavaBlock.EMPTY_JAVABLOCK) {

            deleteJoinPointStatement(goal, pio, services);
            SequentFormula f = goal.sequent().succedent().get(1);
            PosInTerm pit = PosInTerm.getTopLevel();
            pio = new PosInOccurrence(f, pit, false);
        }

        // ImmutableList<Goal> goalsToJoin = null;

        return newGoals;
    }
    //use the one from joinRule.
    private ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> getJoinPartners(
            Goal goal, ImmutableList<Goal> joinGoals, PosInOccurrence pio,
            Services services) {
        ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = ImmutableSLList
                .nil();

        for (Goal g : joinGoals) {

            if (!g.equals(goal) && !g.isLinked()) {
                Semisequent succedent = g.sequent().succedent();

                for (int i = 0; i < succedent.size(); i++) {
                    SequentFormula f = succedent.get(i);

                    PosInTerm pit = PosInTerm.getTopLevel();

                    PosInOccurrence gPio = new PosInOccurrence(f, pit, false);

                    if (JoinRule.isOfAdmissibleForm(g, gPio, false)) {
                        Triple<Term, Term, Term> ownSEState = sequentToSETriple(
                                goal.node(), pio, services);
                        Triple<Term, Term, Term> partnerSEState = sequentToSETriple(
                                g.node(), gPio, services);

                        // NOTE: The equality check for the Java
                        // blocks can be
                        // problematic, since KeY instantiates
                        // declared program
                        // variables with different identifiers;
                        // e.g.
                        // {int x = 10; if (x...)} could get
                        // {x_1 = 10; if (x_1...)}
                        // in one and {x_2 = 10; if (x_2...)} in the
                        // other
                        // branch. This cannot be circumvented with
                        // equalsModRenaming, since at this point,
                        // the PVs are
                        // already declared. We therefore check
                        // equality
                        // modulo switching to branch-unique (and
                        // not globally
                        // unique) names.
                        // TODO: Update this comment above

                        JavaProgramElement ownProgramElem = ownSEState.third
                                .javaBlock().program();
                        JavaProgramElement partnerProgramElem = partnerSEState.third
                                .javaBlock().program();

                        Term ownPostCond = ownSEState.third
                                .op() instanceof Modality
                                        ? ownSEState.third.sub(0)
                                        : ownSEState.third;
                        Term partnerPostCond = partnerSEState.third
                                .op() instanceof Modality
                                        ? partnerSEState.third.sub(0)
                                        : partnerSEState.third;

                        ProgramVariablesMatchVisitor matchVisitor = new ProgramVariablesMatchVisitor(
                                partnerProgramElem, ownProgramElem, services);
                        matchVisitor.start();

                        // Requirement: Same post condition,
                        // matching program
                        // parts.
                        // NOTE: If we have a modality in the post
                        // condition,
                        // the equality of post conditions may be
                        // too strict,
                        // so some legal cases will be excluded from
                        // the join
                        // partners list.
                        if (ownPostCond.equals(partnerPostCond)
                                && !matchVisitor.isIncompatible()) {

                            joinPartners = joinPartners.prepend(
                                    new Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>(
                                            g, gPio, matchVisitor.getMatches()
                                                    .getValue()));

                        }
                    }

                }
            }
        
    }

    return joinPartners;

    }

    private ImmutableList<Goal> getJoinGoals(Goal goal, Services services) {
        ImmutableList<Goal> result = ImmutableSLList.nil();
        ImmutableList<Goal> openGoals = goal.proof().openGoals();
        JavaBlock jB = null;

        for (Goal g : openGoals) {
            if (!g.equals(goal) && !g.isLinked()) {
                Semisequent succedent = g.sequent().succedent();
                for (int i = 0; i < succedent.size(); i++) {
                    SequentFormula f = succedent.get(i);
                    if (f.formula() != null) {
                        jB = JoinRuleUtils.getJavaBlockRecursive(f.formula());
                        if (jB != null && isJoinPointStatement(jB.program())) {
                            result = result.append(g);
                        }
                    }
                }
            }
        }
        return result;
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
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {

        if (pio != null && pio.subTerm().isContainsJavaBlockRecursive()
                && JoinRuleUtils.getJavaBlockRecursive(
                        pio.subTerm()) != JavaBlock.EMPTY_JAVABLOCK
                && isJoinPointStatement(JoinRuleUtils
                        .getJavaBlockRecursive(pio.subTerm()).program())) {
            ImmutableList<Goal> openGoals = goal.proof().openGoals();

            for (Goal g : openGoals) {
                if (!g.equals(goal) && !isJoinPointStatement(JoinRuleUtils
                        .getJavaBlockRecursive(
                                g.sequent().succedent().get(1).formula())
                        .program())) {
                    return false;
                }
            }
            return true;

        }
        else
            return false;

    }

    private boolean isJoinPointStatement(ProgramElement pE) {

        if (pE != null && pE instanceof StatementBlock
                && ((StatementBlock) pE).getInnerMostMethodFrame() != null
                && ((StatementBlock) pE).getInnerMostMethodFrame().getBody()
                        .getFirstElement() instanceof JoinPointStatement)
            return true;

        else
            return false;

    }

    private void deleteJoinPointStatement(Goal goal, PosInOccurrence pio,
            Services services) {

        Term formula = goal.sequent().succedent().get(1).formula();
        JavaBlock jB = JoinRuleUtils.getJavaBlockRecursive(formula);
        ProgramElement pE = jB.program();
        StatementBlock sB = ((StatementBlock) pE).getInnerMostMethodFrame()
                .getBody();
        Statement[] array = new Statement[sB.getBody().toImmutableList().tail()
                .size()];
        // StatementBlock sB2 =
        // KeYJavaASTFactory.block(sB.getBody().toImmutableList().tail().toArray(array));

        MethodFrame frameTemp = KeYJavaASTFactory.methodFrame(
                ((StatementBlock) pE).getInnerMostMethodFrame()
                        .getProgramVariable(),
                ((StatementBlock) pE).getInnerMostMethodFrame()
                        .getExecutionContext(),
                new StatementBlock(
                        sB.getBody().toImmutableList().tail().toArray(array)));

        // try statement
        Try newTryStatement = KeYJavaASTFactory.tryBlock(frameTemp,
                (Catch) ((Try) ((StatementBlock) pE).getBody().get(0))
                        .getChildAt(1));

        Statement newProgram = (Statement) new ProgramElementReplacer(
                (JavaProgramElement) pE, services).replace(
                        ((StatementBlock) pE).getBody().get(0),
                        newTryStatement);

        JavaBlock newJavaBlock = JavaBlock
                .createJavaBlock(newProgram instanceof StatementBlock
                        ? (StatementBlock) newProgram
                        : new StatementBlock(newProgram));

        TermBuilder tb = services.getTermBuilder();
        Term oldTerm = UpdateApplication.getTarget(formula);
        Term newTerm = tb.tf().createTerm(oldTerm.op(), oldTerm.subs(),
                oldTerm.boundVars(), newJavaBlock);

        goal.changeFormula(
                new SequentFormula(tb
                        .apply(UpdateApplication.getUpdate(formula), newTerm)),
                pio);

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

    //toString
}
