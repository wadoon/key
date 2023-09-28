package de.uka.ilkd.key.rule.tuc;

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
import org.key_project.util.collection.ImmutableSLList;

import javax.annotation.Nonnull;

public class ClosedAfterTuc implements BuiltInRule {

    public static final ClosedAfterTuc INSTANCE = new ClosedAfterTuc();
    private static final String DISPLAY_NAME = "CloseAfterTUC";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    private ClosedAfterTuc() {}

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence pio) {
        return true;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(final PosInOccurrence pos, final TermServices services) {
        return new ClosedAfterTucApp(this);
    }

    @Nonnull
    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services, final RuleApp ruleApp) throws RuleAbortException {
        if (!(ruleApp instanceof ClosedAfterTucApp app) || app.getLinkedGoal() == null) {
            throw new RuleAbortException();
        }
        goal.setLinkedGoal(app.getLinkedGoal());
        goal.proof().closeGoal(goal);
        return ImmutableSLList.nil();
    }

    @Override
    public Name name() {
        return RULE_NAME;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    public RuleApp createApp(final Goal goal) {
        return new ClosedAfterTucApp(this, goal);
    }
}
