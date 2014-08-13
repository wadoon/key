package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;


public final class RelyBuiltInRuleApp extends AbstractBuiltInRuleApp {
    
    final RelyRule.Instantiation inst;

    protected RelyBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio) {
        this(rule, pio, null);
    }
    
    RelyBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pio, RelyRule.Instantiation inst) {
        super(rule, pio);
        this.inst = inst;
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new RelyBuiltInRuleApp(rule(), newPos);
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        final RelyRule rule = (RelyRule) rule();
        final Term target = posInOccurrence().constrainedFormula().formula();
        final RelyRule.Instantiation newInst = rule.getInstantiation(target, goal);
        return new RelyBuiltInRuleApp(rule(), posInOccurrence(), newInst);
    }
    
    @Override
    public boolean complete() {
        return isSufficientlyComplete() && inst != null;
    }
    
    @Override
    public boolean isSufficientlyComplete() {
        return posInOccurrence() != null;
    }

}
