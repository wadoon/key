package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.ldt.FloatingPointLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.EnableInProfiles;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.List;

@EnableInProfiles(JavaProfile.class)
public class DaisyBoundsBuiltinRule implements BuiltInRule {
    public static final DaisyBoundsBuiltinRule INSTANCE = new DaisyBoundsBuiltinRule();
    public static final Name NAME = new Name("Daisy Bounds Rule");

    /**
     * Finds bounds on floating point variables on the sequent,
     * i.e., terms of the form "x cmp c" where x is a float expression,
     * cmp a comparator and c a floating point literal (possibly negated).
     * @param sequent the current sequent
     * @param ldt
     * @return a list of terms representing bounds on fp variables
     */
    private List<Term> gatherPreconditions(Sequent sequent, FloatingPointLDT ldt, Services services) {
        List<Term> res = new ArrayList<>();
        ImmutableList<SequentFormula> anteFormulas = sequent.antecedent().asList();
        for (SequentFormula sf : anteFormulas) {
            Operator op = sf.formula().op();
            if (isCmp(op, ldt) && isValueComparison(sf.formula(), ldt)) {
                res.add(sf.formula());
            }
        }
        TermFactory tf = new TermFactory();
        TermBuilder tb = new TermBuilder(tf, services);
        ImmutableList<SequentFormula> succFormulas = sequent.succedent().asList();
        for (SequentFormula sf : succFormulas) {
            Operator op = sf.formula().op();
            if (isCmp(op, ldt) && isValueComparison(sf.formula(), ldt)) {
                Term negated = tb.not(sf.formula());
                res.add(negated);
            }
        }
        return res;
    }

    /**
     * @param t A term representing a floating point comparison
     * @return true iff one of the subterms is a (possibly negated) float literal
     */
    private boolean isValueComparison(Term t, FloatingPointLDT ldt) {
        Operator op0 = t.sub(0).op(), op1 = t.sub(1).op();
        Function literalSymbol = ldt.getLiteralSymbol();
        Function javaUnaryMinus = ldt.getJavaUnaryMinus();
        return (op0 == literalSymbol || op0 == javaUnaryMinus || op1 == literalSymbol || op1 == javaUnaryMinus) && (t.sub(0).subs().size() == 0 || t.sub(1).subs().size() == 0);
    }

    private boolean isCmp(Operator op, FloatingPointLDT ldt) {
        return op == ldt.getGreaterThan()
                || op == ldt.getGreaterOrEquals()
                || op == ldt.getLessThan()
                || op == ldt.getLessOrEquals()
                || op == ldt.getEquals();
    }

    private List<Term> gatherLetExprs(Sequent sequent, FloatingPointLDT ldt) {
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
        return DaisyAPI.computeFloatRange(preconditions,floatExpr,lets,services);
    }

    private Pair<Double, Double> daisyComputeDoubleBounds(List<Term> preconditions, List<Term> lets, Term floatExpr, Services services) {
        return DaisyAPI.computeDoubleRange(preconditions,floatExpr,lets,services);
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null) return false;
        Services services = goal.proof().getServices();
        Operator op = pio.subTerm().op();
        return isFloatOp(op, services) || isDoubleOp(op, services);
    }

    private boolean isFloatOp(Operator op, Services services) {
        FloatLDT floatLDT = new FloatLDT(services);
        return (op == floatLDT.getAdd()
                || op == floatLDT.getSub()
                || op == floatLDT.getMul()
                || op == floatLDT.getDiv());
    }

    private boolean isDoubleOp(Operator op, Services services) {
        DoubleLDT doubleLDT = new DoubleLDT(services);
        return (op == doubleLDT.getAdd()
                || op == doubleLDT.getSub()
                || op == doubleLDT.getMul()
                || op == doubleLDT.getDiv());
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
        FloatingPointLDT ldt = isFloat ? new FloatLDT(services) : new DoubleLDT(services);
        Sequent seq = goal.sequent();
        List<Term> precs = gatherPreconditions(seq, ldt, services);
        List<Term> letExprs = gatherLetExprs(seq, ldt);
        TermBuilder tb = services.getTermBuilder();
        final ImmutableList<Goal> result = goal.split(1);
        final Goal resultGoal = result.head();
        Term upperTerm, lowerTerm;
        if (isFloat) {
            Pair<Float, Float> bounds = daisyComputeFloatBounds(precs, letExprs, expr, services);
            lowerTerm = floatToTerm(bounds.first, services);
            upperTerm = floatToTerm(bounds.second, services);
        } else { //double
            Pair<Double, Double> bounds = daisyComputeDoubleBounds(precs, letExprs, expr, services);
            lowerTerm = doubleToTerm(bounds.first, services);
            upperTerm = doubleToTerm(bounds.second, services);
        }
        Term resLower = tb.func(ldt.getGreaterOrEquals(), expr, lowerTerm);
        Term resUpper = tb.func(ldt.getLessOrEquals(), expr, upperTerm);
        resultGoal.addFormula(new SequentFormula(resLower), true, false);
        resultGoal.addFormula(new SequentFormula(resUpper), true, false);
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
