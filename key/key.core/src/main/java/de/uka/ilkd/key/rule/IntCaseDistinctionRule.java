package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (6/3/21)
 */
public class IntCaseDistinctionRule implements BuiltInRule {
    public static final IntCaseDistinctionRule INSTANCE = new IntCaseDistinctionRule();


    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio != null) {
            Term t = pio.subTerm();
            Sort intSort = goal.proof().getServices().getNamespaces().sorts().lookup("int");
            return t.op() instanceof LocationVariable && t.sort() == intSort;
        }
        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return true;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new IntCaseDistinctionRuleApp(pos);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {
        IntCaseDistinctionRuleApp app = (IntCaseDistinctionRuleApp) ruleApp;
        Term selectedTerm = app.posInOccurrence().subTerm();

        int lower = app.lower;
        int upper = app.upper;
        int numElements = upper - lower + 1;
        int numGoals = numElements + 2; // +1 for smaller && +1 for larger than range
        ImmutableList<Goal> ngoals = goal.split(numGoals);
        List<Goal> seq = ngoals.toList();
        TermBuilder tb = goal.proof().getServices().getTermBuilder();

        for (int i = 0; i < seq.size(); i++) {
            int value = lower + i;
            boolean isLt = i == seq.size() - 2;
            boolean isGt = i == seq.size() - 1;
            Goal g = seq.get(i);

            if (isLt) g.setBranchLabel(selectedTerm.toString() + " < " + lower);
            else if (isGt) g.setBranchLabel(selectedTerm.toString() + " > " + upper);
            else g.setBranchLabel(selectedTerm.toString() + " = " + value);

            Term eqTerm;
            if (isLt) eqTerm = tb.lt(selectedTerm, tb.zTerm(lower));
            else if (isGt) eqTerm = tb.gt(selectedTerm, tb.zTerm(lower));
            else eqTerm = tb.equals(selectedTerm, tb.zTerm(value));

            SequentFormula equality = new SequentFormula(eqTerm);
            ImmutableList<SequentFormula> sf = ImmutableSLList.singleton(equality);
            SequentChangeInfo change = g.sequent().addFormula(sf, true, true);
            g.setSequent(change);
        }

        return ngoals;
    }

    @Override
    public Name name() {
        return new Name("int_cases_distinction");
    }

    @Override
    public String displayName() {
        return "int_cases_distinction";
    }

    public static class IntCaseDistinctionRuleApp extends DefaultBuiltInRuleApp {
        Integer lower, upper;

        public IntCaseDistinctionRuleApp(PosInOccurrence pos) {
            super(INSTANCE, pos);
        }

        @Override
        public boolean complete() {
            return lower != null && upper != null;
        }

        public void setRange(int lower, int upper) {
            this.lower = lower;
            this.upper = upper;
        }
    }
}
