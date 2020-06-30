package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import org.key_project.util.collection.ImmutableList;

public class DaisyBoundsBuiltinRule implements BuiltInRule {
    public static final DaisyBoundsBuiltinRule INSTANCE = new DaisyBoundsBuiltinRule();

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
