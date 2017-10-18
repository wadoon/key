package de.uka.ilkd.key.dependencycluster.po;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;

//TODO JK make this unugly
public class AgreeTacletFactory {
    
    private final String ruleNameSuffix;
    private final ImmutableList<Term> lowState;
    private final InitConfig proofConfig;
    private final TermBuilder tb;
    private final Function agreePreFunction;
    private final Function agreePostFunction;
    private final Term heap1;
    private final Term heap2;

    public AgreeTacletFactory(ImmutableList<Term> lowState, InitConfig proofConfig, String ruleNameSuffix, Function agreePreFunction, Function agreePostFunction) {
        this.ruleNameSuffix = ruleNameSuffix;
        this.lowState = lowState;
        this.proofConfig = proofConfig;
        tb = proofConfig.getServices().getTermBuilder();
        this.agreePreFunction = agreePreFunction;
        this.agreePostFunction = agreePostFunction;
        
        Sort heapSort = proofConfig.getServices().getTypeConverter().getHeapLDT().targetSort();
        heap1 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap1"), heapSort, false, false));
        heap2 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap2"), heapSort, false, false));
    }
    
    public RewriteTaclet getAgreePreTaclet() {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        final String name = "AAAAgreePre" + ruleNameSuffix;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));
        
        tacletBuilder.setFind(tb.func(agreePreFunction, heap1, heap2));
        
        tacletBuilder.addGoalTerm(agreePre());
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)proofConfig.ruleSetNS().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    private Term agreePre() {
        ImmutableList<Term> collectedTerms = ImmutableSLList.<Term>nil();
        for (Term t: lowState) {
            System.out.println(t);
            Term t1 = tb.apply(tb.elementary(tb.getBaseHeap(), heap2), t);
            Term t2 = tb.apply(tb.elementary(tb.getBaseHeap(), heap1), t);
            collectedTerms = collectedTerms.append(tb.equals(t1, t2));
        }
        return tb.and(collectedTerms);
    }

    //TODO JK AgreePost is object sensitive - if we use it this has to be implemented properly
    public RewriteTaclet getAgreePostTaclet() {
        return null;
    }
}
