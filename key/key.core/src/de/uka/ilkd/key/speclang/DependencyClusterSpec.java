package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.RewriteTaclet;

public interface DependencyClusterSpec {

    public Function getEquivEventEqPredicate();
    
    public Function getEquivEventIsoPredicate();
    
    public Function getAgreePrePredicate();
    
    public Function getVisibilityPredicate();
    
    public void registerPredicatesAndTaclets();

}
