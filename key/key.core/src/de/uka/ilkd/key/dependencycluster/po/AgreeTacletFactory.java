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
    private final Term contractSelf;
    private final Term specSelf;

    /*
     * separate self variables are needed if the self in the lowState specification (specSelf) 
     * isn't the same as the self used in the proof obligation these taclets are used in (contractSelf).
     * We set {specSelf:=contractSelf}.
     */
    public AgreeTacletFactory(ImmutableList<Term> lowState, Term contractSelf, Term specSelf, Services services, String ruleNameSuffix, Function agreePreFunction, Function agreePostFunction) {
        this.ruleNameSuffix = ruleNameSuffix;
        this.lowState = lowState;
        this.services = services;
        tb = services.getTermBuilder();
        this.agreePreFunction = agreePreFunction;
        this.agreePostFunction = agreePostFunction;
        this.contractSelf = contractSelf;
        this.specSelf = specSelf;
                        
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
            //TODO JK less ugly
            Term t1 = tb.apply(tb.elementary(tb.getBaseHeap(), heap2), t);
            Term t2 = tb.apply(tb.elementary(tb.getBaseHeap(), heap1), t);
            
            if (contractSelf.equals(specSelf)) {
                collectedTerms = collectedTerms.append(tb.equals(t1, t2));
            } else {
                Term tt1 = tb.apply(tb.elementary(specSelf, contractSelf), t1);
                Term tt2 = tb.apply(tb.elementary(specSelf, contractSelf), t2);
                collectedTerms = collectedTerms.append(tb.equals(tt1, tt2));
            }
        }
        return tb.and(collectedTerms);
    }
    
    //TODO JK this isn't quite agreePost as in theory but a special version for cluster satisfaction contracts - make this obvious!
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


    //TODO JK If I understood correctly, Simon says (heh...) we can ignore any new objects business here. Maybe think about this another time - after all, for objects existing in the prestate not any isomorphism is good enough in the poststate, and there are a few other issues. But, of course, we don't really deal with pre- and poststates here, we're only really thinking in Terms of information subsets...
    private Term agreePost() {
        Function objectsIsoFunction =
                (Function)services.getNamespaces().functions().lookup("objectsIsomorphic");
        Function sameTypesFunction =
                (Function)services.getNamespaces().functions().lookup("sameTypes");
        Function agreeBasicFunction = services.getTypeConverter().getServiceEventLDT().getAgreeBasic();
        
        Term lowSeq = tb.seq(lowState);
        Term t1;
        Term t2;
        if (contractSelf.equals(specSelf)) {
            t1 = tb.apply(tb.elementary(tb.getBaseHeap(), heap1), lowSeq);
            t2 = tb.apply(tb.elementary(tb.getBaseHeap(), heap2), lowSeq);
        } else {
            t1 = tb.apply(tb.elementary(specSelf, contractSelf), tb.apply(tb.elementary(tb.getBaseHeap(), heap1), lowSeq));
            t2 = tb.apply(tb.elementary(specSelf, contractSelf), tb.apply(tb.elementary(tb.getBaseHeap(), heap2), lowSeq));
        }
        
        Term sameTypes = tb.func(sameTypesFunction, t1, t2);
        Term agreeBasic = tb.func(agreeBasicFunction, t1, t2);
        Term objectsIso = tb.func(objectsIsoFunction, t1, t1, t2, t2);
        
        return tb.and(sameTypes, agreeBasic, objectsIso);
    }

}
