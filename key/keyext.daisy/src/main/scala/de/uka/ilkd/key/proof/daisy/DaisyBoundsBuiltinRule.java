package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.FloatLiteral;
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
    public static final Name NAME = new Name("Daisy Bounds Rule");

    private List<Term> gatherPreconditions(Sequent sequent, Services services) {
        List<Term> res = new ArrayList<>();
        FloatLDT floatLDT = new FloatLDT(services);
        ImmutableList<SequentFormula> anteFormulas = sequent.antecedent().asList();
        for (SequentFormula sf : anteFormulas) {
            Operator op = sf.formula().op();
            if (isFloatCmp(op, floatLDT) && isFloatLitCmp(sf.formula(), floatLDT)) {
                res.add(sf.formula());
            }
        }
        return res;
    }

    // return true if the term has 2 subterms and (at least) one of them is a float literal.
    // if both are literals, we don't need the term, but it does not hurt either.
    private boolean isFloatLitCmp(Term t, FloatLDT floatLDT) {
        return t.subs().size() == 2
                && (t.sub(0).op() == floatLDT.getFloatSymbol()
                    || t.sub(1).op() == floatLDT.getFloatSymbol());
    }

    private boolean isFloatCmp(Operator op, FloatLDT floatLDT) {
        return op == floatLDT.getGreaterThan()
                || op == floatLDT.getGreaterOrEquals()
                || op == floatLDT.getLessThan()
                || op == floatLDT.getLessOrEquals();
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
    private Pair<Float, Float> daisyComputeBounds(List<Term> preconditions, List<Term> lets, Term floatExpr, Services services) {

        return DaisyAPI.computeRange(preconditions,floatExpr,lets,services);
    }

    @Override
    // must return false if some bounds are not specified
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        Services services = goal.proof().getServices();
        FloatLDT floatLDT = new FloatLDT(services);
        if (pio == null) return false;
        Operator op = pio.subTerm().op();
        boolean res = (op == floatLDT.getJavaAdd()
                || op == floatLDT.getJavaSub()
                || op == floatLDT.getJavaMul()
                || op == floatLDT.getJavaDiv());
        return res;
    }

    @Override
    //
    public boolean isApplicableOnSubTerms() {
        return true;
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
        Pair<Float, Float> bounds = daisyComputeBounds(precs, letExprs, expr, services);
        Float lower = bounds.first;
        FloatLiteral lowerLit = new FloatLiteral(lower);
        Float upper = bounds.second;
        FloatLiteral upperLit = new FloatLiteral(upper);
        FloatLDT floatLDT = new FloatLDT(services);
        Term lowerTerm = floatLDT.translateLiteral(lowerLit, services);
        Term upperTerm = floatLDT.translateLiteral(upperLit, services);

        final ImmutableList<Goal> result = goal.split(1);
        final Goal resultGoal = result.head();
        TermFactory tf = new TermFactory();
        TermBuilder tb = new TermBuilder(tf, services);

        Term resLower = tb.func(floatLDT.getGreaterOrEquals(), expr, lowerTerm);
        Term resUpper = tb.func(floatLDT.getLessOrEquals(), expr, upperTerm);
        resultGoal.addFormula(new SequentFormula(resLower), true, false);
        resultGoal.addFormula(new SequentFormula(resUpper), true, false);

        return result;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return NAME.toString();
    }
}
