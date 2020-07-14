package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.List;

public class DaisyBoundsBuiltinRule implements BuiltInRule {
    public static final DaisyBoundsBuiltinRule INSTANCE = new DaisyBoundsBuiltinRule();

    private List<Term> gatherPreconditions(Sequent sequent, Services services) {
        List<Term> res = new ArrayList<>();
        FloatLDT floatLDT = new FloatLDT(services);
        ImmutableList<SequentFormula> anteFormulas = sequent.antecedent().asList();
        for (SequentFormula sf : anteFormulas) {
            Operator op = sf.formula().op();
            if (op == floatLDT.getGreaterThan()
                || op == floatLDT.getGreaterOrEquals()
                || op == floatLDT.getLessThan()
                || op == floatLDT.getLessOrEquals()) {
                res.add(sf.formula());
            }
        }
        return res;
    }

    private List<Term> gatherLetExprs(Sequent sequent, Services services) {
        List<Term> res = new ArrayList<>();
        FloatLDT floatLDT = new FloatLDT(services);
        ImmutableList<SequentFormula> anteFormulas = sequent.antecedent().asList();
        for (SequentFormula sf : anteFormulas) {
            Operator op = sf.formula().op();
            if (op == floatLDT.getEquals()) {
                res.add(sf.formula());
            }
        }
        return res;
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
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ra) throws RuleAbortException {
        Sequent seq = goal.sequent();
        List<Term> precs = gatherPreconditions(seq, services);
        List<Term> letExprs = gatherLetExprs(seq, services);
        Term expr = ((DaisyBoundsRuleApp) ra).getExpr();
        Pair<Float, Float> bounds = daisyComputeBounds(precs, letExprs, expr);

        final ImmutableList<Goal> result = goal.split(1);
        final Goal resultGoal = result.head();

        // TODO js: build the terms (using term builder, probably)
        resultGoal.addFormula(expr < bounds.second, ra.posInOccurrence());
        resultGoal.addFormula(expr > bounds.first, ra.posInOccurrence());

        return result;
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
