package de.uka.ilkd.key.loopinvgen;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;

public class ShiftUpdateRule implements BuiltInRule {

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Name name() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String displayName() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        // TODO Auto-generated method stub
        return null;
    }

}
