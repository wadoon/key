package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.ldt.IFloatingPointLDT;
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

    /**
     * Finds bounds on floating point variables on the sequent,
     * i.e., terms of the form "x cmp c" where x is a float variable,
     * cmp a comparator and c a floating point literal.
     * @param sequent the current sequent
     * @param services
     * @return a list of terms representing bounds on fp variables
     */
    private List<Term> gatherPreconditions(Sequent sequent, IFloatingPointLDT ldt, Services services) {
        List<Term> res = new ArrayList<>();
        ImmutableList<SequentFormula> anteFormulas = sequent.antecedent().asList();
        for (SequentFormula sf : anteFormulas) {
            Operator op = sf.formula().op();
            if (isCmp(op, ldt) && isLitCmp(sf.formula(), ldt)) {
                res.add(sf.formula());
            }
        }
        TermFactory tf = new TermFactory();
        TermBuilder tb = new TermBuilder(tf, services);
        ImmutableList<SequentFormula> succFormulas = sequent.succedent().asList();
        for (SequentFormula sf : succFormulas) {
            Operator op = sf.formula().op();
            if (isCmp(op, ldt) && isLitCmp(sf.formula(), ldt)) {
                Term negated = tb.not(sf.formula());
                res.add(negated);
            }
        }
        return res;
    }

    // return true if both subterms are either float literals or simple variables
    private boolean isLitCmp(Term t, IFloatingPointLDT ldt) {
        if (ldt instanceof FloatLDT) {
            FloatLDT fldt = (FloatLDT) ldt;
            return (t.sub(0).subs().size() == 0 || t.sub(0).op() == fldt.getFloatSymbol())
                    && (t.sub(1).subs().size() == 0 || t.sub(1).op() == fldt.getFloatSymbol());
        } else if (ldt instanceof DoubleLDT) {
            DoubleLDT dldt = (DoubleLDT) ldt;
            return (t.sub(0).subs().size() == 0 || t.sub(0).op() == dldt.getDoubleSymbol())
                    && (t.sub(1).subs().size() == 0 || t.sub(1).op() == dldt.getDoubleSymbol());
        } else { //should be unreachable
            return false;
        }
    }

    private boolean isCmp(Operator op, IFloatingPointLDT ldt) {
        return op == ldt.getGreaterThan()
                || op == ldt.getGreaterOrEquals()
                || op == ldt.getLessThan()
                || op == ldt.getLessOrEquals();
    }

    private List<Term> gatherLetExprs(Sequent sequent, IFloatingPointLDT ldt) {
        List<Term> res = new ArrayList<>();
        ImmutableList<SequentFormula> anteFormulas = sequent.antecedent().asList();
        for (SequentFormula sf : anteFormulas) {
            Operator op = sf.formula().op();
            if (op == ldt.getEquals()) {
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
    private Pair<Float, Float> daisyComputeFloatBounds(List<Term> preconditions, List<Term> lets, Term floatExpr, Services services) {
        return DaisyAPI.computeRange(preconditions,floatExpr,lets,services);
    }

    private Pair<Double, Double> daisyComputeDoubleBounds(List<Term> preconditions, List<Term> lets, Term floatExpr, Services services) {
        return DaisyAPI.computeDoubleRange(preconditions,floatExpr,lets,services);
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return isFloatApplicable(goal, pio) || isDoubleApplicable(goal, pio);
    }

    // must return false if some bounds are not specified
    public boolean isFloatApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null) return false;
        Services services = goal.proof().getServices();
        Operator op = pio.subTerm().op();
        return isFloatOp(op, services);
    }

    private boolean isFloatOp(Operator op, Services services) {
        FloatLDT floatLDT = new FloatLDT(services);
        boolean res = (op == floatLDT.getAddIEEE()
                || op == floatLDT.getSubIEEE()
                || op == floatLDT.getMulIEEE()
                || op == floatLDT.getDivIEEE());
        return res;
    }

    // must return false if some bounds are not specified
    public boolean isDoubleApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null) return false;
        Services services = goal.proof().getServices();
        Operator op = pio.subTerm().op();
        return isDoubleOp(services, op);
    }

    private boolean isDoubleOp(Services services, Operator op) {
        DoubleLDT doubleLDT = new DoubleLDT(services);
        boolean res = (op == doubleLDT.getAddIEEE()
                || op == doubleLDT.getSubIEEE()
                || op == doubleLDT.getMulIEEE()
                || op == doubleLDT.getDivIEEE());
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
        Term expr = ((DaisyBoundsRuleApp) ra).getExpr();
        boolean isFloat = isFloatOp(expr.op(), services);
        IFloatingPointLDT ldt = isFloat ? new FloatLDT(services) : new DoubleLDT(services);
        Sequent seq = goal.sequent();
        List<Term> precs = gatherPreconditions(seq, ldt, services);
        List<Term> letExprs = gatherLetExprs(seq, ldt);
        TermBuilder tb = services.getTermBuilder();
        final ImmutableList<Goal> result = goal.split(1);
        if (isFloat) {
            Pair<Float, Float> bounds = daisyComputeFloatBounds(precs, letExprs, expr, services);
            Term lowerTerm = floatToTerm(bounds.first, services);
            Term upperTerm = floatToTerm(bounds.second, services);

            final Goal resultGoal = result.head();

            Term resLower = tb.func(ldt.getGreaterOrEquals(), expr, lowerTerm);
            Term resUpper = tb.func(ldt.getLessOrEquals(), expr, upperTerm);
            resultGoal.addFormula(new SequentFormula(resLower), true, false);
            resultGoal.addFormula(new SequentFormula(resUpper), true, false);
        } else {
            Pair<Double, Double> bounds = daisyComputeDoubleBounds(precs, letExprs, expr, services);
            Term lowerTerm = doubleToTerm(bounds.first, services);
            Term upperTerm = doubleToTerm(bounds.second, services);

            final Goal resultGoal = result.head();

            Term resLower = tb.func(ldt.getGreaterOrEquals(), expr, lowerTerm);
            Term resUpper = tb.func(ldt.getLessOrEquals(), expr, upperTerm);
            resultGoal.addFormula(new SequentFormula(resLower), true, false);
            resultGoal.addFormula(new SequentFormula(resUpper), true, false);
        }
        return result;
    }

    private Term doubleToTerm(Double d, Services services) {
        return services.getTermBuilder().dfpTerm(d);
    }

    private Term floatToTerm(Float f, Services services) {
       return services.getTermBuilder().fpTerm(f);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return NAME.toString();
    }

    @Override
    public String toString() {
        return displayName();
    }
}
