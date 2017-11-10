package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.RewriteTaclet;

public interface DependencyClusterSpec {
    
    public String getLabel();

    public Function getEquivEventEqPredicate();
    
    public Function getEquivEventIsoPredicate();
    
    public Function getAgreePrePredicate();
    
    public Function getAgreePostPredicate();
    
    public Function getVisibilityPredicate();
    
    public void registerPredicates();
    
    public ImmutableList<RewriteTaclet> getTaclets(Term self, InitConfig config);

}
