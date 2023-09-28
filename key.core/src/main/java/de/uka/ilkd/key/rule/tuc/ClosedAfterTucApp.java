package de.uka.ilkd.key.rule.tuc;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import org.key_project.util.collection.ImmutableList;

public class ClosedAfterTucApp extends AbstractBuiltInRuleApp {

    private Goal linkedGoal;

    public ClosedAfterTucApp(final ClosedAfterTuc closedAfterTuc) {
        super(closedAfterTuc, null);
    }

    public ClosedAfterTucApp(final ClosedAfterTuc closedAfterTuc, final Goal goal) {
        super(closedAfterTuc, null);
        linkedGoal = goal;
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(final PosInOccurrence newPos) {
        return null;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(final ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(final Goal goal) {
        return this;
    }

    @Override
    public boolean complete() {
        return linkedGoal != null;
    }

    public Goal getLinkedGoal() {
        return linkedGoal;
    }

    public void setLinkedGoal(final Goal linkedGoal) {
        this.linkedGoal = linkedGoal;
    }
}
