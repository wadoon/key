package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
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
    private List<Term> gatherPreconditions() {
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
        return null;
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return null;
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {
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
