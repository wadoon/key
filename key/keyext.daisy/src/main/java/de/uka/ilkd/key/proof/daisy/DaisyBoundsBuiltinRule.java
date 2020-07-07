package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.List;

public class DaisyBoundsBuiltinRule implements BuiltInRule {
    public static final DaisyBoundsBuiltinRule INSTANCE = new DaisyBoundsBuiltinRule();

    // TODO js
    private List<Term> gatherPreconditions(Sequent sequent) {
        return null;
    }

    // TODO js
    private List<Term> gatherLetExprs(Sequent sequent) {
        return null;
    }

    // TODO rosa/fahia
    /** @param preconditions have the form
            floatVar cmp floatLiteral (where cmp is <, <=, >=, or >)
       @param lets have the form
            floatVar = expr
        they can be translated as let-expressions in scala.
       @param floatExpr the expression for which bounds are to be computed
       @return a lower and upper bound for the floating point expression
     */
    private Pair<Float, Float> daisyComputeBounds(List<Term> preconditions, List<Term> lets, Term floatExpr) {

        return DaisyAPI.computeRange(preconditions,floatExpr,lets);
    }

    @Override
    // must return false if some bounds are not specified
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public DaisyBoundsRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DaisyBoundsRuleApp(this, pos);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {
        Sequent seq = goal.sequent();
        List<Term> precs = gatherPreconditions(seq);
        List<Term> letExprs = gatherLetExprs(seq);
        Pair<Float, Float> bounds = daisyComputeBounds(precs, letExprs, ruleApp.expr);
        return null;
    }

    @Override
    public Name name() {
        return null;
    }

    @Override
    public String displayName() {
        return null;
    }
}
