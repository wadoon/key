package de.uka.ilkd.key.rule.join;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

public class DeleteJoinPointBuiltInRuleApp extends AbstractBuiltInRuleApp{

    public DeleteJoinPointBuiltInRuleApp(final BuiltInRule rule, final PosInOccurrence occurrence) {
        super(rule, occurrence);
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        // TODO Auto-generated method stub
        return this;
    }

}
