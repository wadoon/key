package de.uka.ilkd.key.dependencycluster.po;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
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
    public static final String AGREE_PRE_RULE_BASENAME = "AAADefOfAgreePre";
    public static final String AGREE_POST_RULE_BASENAME = "AAADefOfAgreePost";
    
    private final String ruleNameSuffix;
    private final ImmutableList<Term> lowState;
    private final Services services;
    private final TermBuilder tb;
    private final Function agreePreFunction;
    private final Function agreePostFunction;
    private final Term heap1;
    private final Term heap2;

    public AgreeTacletFactory(ImmutableList<Term> lowState, Services services, String ruleNameSuffix, Function agreePreFunction, Function agreePostFunction) {
        this.ruleNameSuffix = ruleNameSuffix;
        this.lowState = lowState;
        this.services = services;
        tb = services.getTermBuilder();
        this.agreePreFunction = agreePreFunction;
        this.agreePostFunction = agreePostFunction;
        
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        heap1 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap1"), heapSort, false, false));
        heap2 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap2"), heapSort, false, false));
    }
    
    public RewriteTaclet getAgreePreTaclet() {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        final String name = AGREE_PRE_RULE_BASENAME + ruleNameSuffix;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));
        
        tacletBuilder.setFind(tb.func(agreePreFunction, heap1, heap2));
        
        tacletBuilder.addGoalTerm(agreePre());
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)services.getNamespaces().ruleSets().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    private Term agreePre() {
        ImmutableList<Term> collectedTerms = ImmutableSLList.<Term>nil();
        for (Term t: lowState) {
            Term t1 = tb.apply(tb.elementary(tb.getBaseHeap(), heap2), t);
            Term t2 = tb.apply(tb.elementary(tb.getBaseHeap(), heap1), t);
            collectedTerms = collectedTerms.append(tb.equals(t1, t2));
        }
        return tb.and(collectedTerms);
    }
    
    public RewriteTaclet getAgreePostTaclet() {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        final String name = AGREE_POST_RULE_BASENAME + ruleNameSuffix;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));
        
        tacletBuilder.setFind(tb.func(agreePostFunction, heap1, heap2));
        
        tacletBuilder.addGoalTerm(agreePost());
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)services.getNamespaces().ruleSets().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }

    private Term agreePost() {
        //TODO JK proper definition of agreePost
        return tb.tt();
    }

}
