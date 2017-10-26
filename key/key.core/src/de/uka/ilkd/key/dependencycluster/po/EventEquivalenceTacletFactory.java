package de.uka.ilkd.key.dependencycluster.po;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.ldt.RemoteMethodEventLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.util.Lowlist;
import de.uka.ilkd.key.util.VisibilityCondition;

public abstract class EventEquivalenceTacletFactory {

    protected final Services services;
    protected final TermBuilder tb;
    protected final RemoteMethodEventLDT ldt;
    
    protected final Term calltype1;
    protected final Term calltype2;
    
    protected final Term caller1;
    protected final Term caller2;
        
    protected final Term callee1;
    protected final Term callee2;
    
    protected final Term service1;
    protected final Term service2;
    
    protected final Term params1;
    protected final Term params2;
    
    protected final Term heap1;
    protected final Term heap2;
    
    protected final Term event1;
    protected final Term event2;
    
    protected final Term updatedParams1;
    protected final Term updatedParams2;
    
    protected final ImmutableList<Lowlist> lowIn;
    protected final ImmutableList<Lowlist> lowOut;
    protected final ImmutableList<VisibilityCondition> visible;
    
    private final Function equivEventFunction;
    private final Function invEventFunction;
    
    private final String ruleNameSuffix;
    
    public EventEquivalenceTacletFactory(Services services, ImmutableList<Lowlist> lowIn, ImmutableList<Lowlist> lowOut, 
            ImmutableList<VisibilityCondition> visible, Function equivEventFunction, Function invEventFunction, String ruleNameSuffix) {

        this.services = services;
        ldt = services.getTypeConverter().getRemoteMethodEventLDT();
        
        this.lowIn = lowIn;
        this.lowOut = lowOut;
        this.visible = visible;
        
        tb = services.getTermBuilder();
        
        Sort calltypeSort = (Sort) services.getNamespaces().sorts().lookup("EventType");
        Sort objectSort = (Sort) services.getNamespaces().sorts().lookup("java.lang.Object");
        Sort methodSort = (Sort) services.getNamespaces().sorts().lookup("MethodIdentifier");
        Sort seqSort = services.getTypeConverter().getSeqLDT().targetSort();
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        
        calltype1 = tb.var(SchemaVariableFactory.createTermSV(new Name("calltype1"), calltypeSort, false, false));
        calltype2 = tb.var(SchemaVariableFactory.createTermSV(new Name("calltype2"), calltypeSort, false, false));
                
        caller1 = tb.var(SchemaVariableFactory.createTermSV(new Name("caller1"), objectSort, false, false));
        caller2 = tb.var(SchemaVariableFactory.createTermSV(new Name("caller2"), objectSort, false, false));
        
        callee1 = tb.var(SchemaVariableFactory.createTermSV(new Name("callee1"), objectSort, false, false));
        callee2 = tb.var(SchemaVariableFactory.createTermSV(new Name("callee2"), objectSort, false, false));
        
        service1 = tb.var(SchemaVariableFactory.createTermSV(new Name("service1"), methodSort, false, false));
        service2 = tb.var(SchemaVariableFactory.createTermSV(new Name("service2"), methodSort, false, false));
        
        params1 = tb.var(SchemaVariableFactory.createTermSV(new Name("params1"), seqSort, false, false));
        params2 = tb.var(SchemaVariableFactory.createTermSV(new Name("params2"), seqSort, false, false));
        
        heap1 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap1"), heapSort, false, false));
        heap2 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap2"), heapSort, false, false));        
        
        event1 = tb.evConst(calltype1, caller1, callee1, service1, params1, heap1);
        event2 = tb.evConst(calltype2, caller2, callee2, service2, params2, heap2);
        
        updatedParams1 = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(ldt.getCurrentParams(), params1));
        updatedParams2 = tb.parallel(tb.elementary(tb.getBaseHeap(), heap2), tb.elementary(ldt.getCurrentParams(), params2));
        
        this.equivEventFunction = equivEventFunction;
        this.invEventFunction = invEventFunction;
        this.ruleNameSuffix = ruleNameSuffix;
    }
    
    public Term findTermEquivalence() {
        Term find = tb.func(equivEventFunction, event1, event2);
        return find;
    }
    
    public Term bothEventsInvisible() {
        Term event1Invis = tb.func(invEventFunction, event1);
        Term event2Invis = tb.func(invEventFunction, event2);
        Term bothInvis = tb.and(event1Invis, event2Invis);
        return bothInvis;
    }
    
    public Term bothEventsVisible() {
        Term event1Vis = tb.not(tb.func(invEventFunction, event1));
        Term event2Vis = tb.not(tb.func(invEventFunction, event2));
        Term bothVis = tb.and(event1Vis, event2Vis);
        return bothVis;
    }
    
    public Term equalMetadata() {
        Term equalType = tb.equals(calltype1, calltype2);
        Term equalCaller = tb.equals(caller1, caller2);
        Term equalCallee = tb.equals(callee1, callee2);
        Term equalService = tb.equals(service1, service2);
        Term equalMetadata = tb.and(equalType, equalCaller, equalCallee, equalService);
        return equalMetadata;
    }
    
    public abstract Term equivalenceForMessagesWithoutLowPart();
    
    public abstract Term invisibilityForMessagesWithoutSpec();
    
    public Term equivalenceInVisibleCase() {
        Term visibleEquivalence = tb.and(bothEventsVisible(), equalMetadata(), tb.and(collectedConditionsForEquivalenceOfVisibleEvents()));
        return visibleEquivalence;
    }
    
    public Term replaceTermEquivalence() {
        Term replaceWith = tb.or(bothEventsInvisible(), equivalenceInVisibleCase());
        return replaceWith;
    }
    
    public RewriteTaclet getEventEquivalenceTaclet() {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        final String name = "AAAEquivEventDef" + ruleNameSuffix;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));
        
        tacletBuilder.setFind(findTermEquivalence());
        
        tacletBuilder.addGoalTerm(replaceTermEquivalence());
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)services.getNamespaces().ruleSets().lookup(new Name("simplify_enlarging")));  
        
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    public RewriteTaclet getInvisibilityTaclet() {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        final String name = "AAAEventInvisibilityDef" + ruleNameSuffix;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));

        tacletBuilder.setFind(findTermInvisibility());
        tacletBuilder.addGoalTerm(replaceTermInvisibility());
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)services.getNamespaces().ruleSets().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    public Term replaceTermInvisibility() {
        return tb.or(tb.not(eventVisibleDueToExplicitSpec()), invisibilityForMessagesWithoutSpec());
    }

    public abstract Term eventVisibleDueToExplicitSpec();
    
    public Term findTermInvisibility() {
        return tb.func(invEventFunction, event1);
    }

    public ImmutableList<Term> collectedConditionsForEquivalenceOfVisibleEvents() {
        ImmutableList<Term> collectedConditionsForEquivalenceOfVisibleEvents = equivalenceConditionsForLowlist(lowIn);
        collectedConditionsForEquivalenceOfVisibleEvents = collectedConditionsForEquivalenceOfVisibleEvents.append(equivalenceConditionsForLowlist(lowOut));
        
        //TODO JK I think I don't need this at all, since equivalenceConditionsForLowlist returns implications there are only equivalence restrictions for messages with low parts
        //Term equivalenceForMessagesWithoutLowPart = equivalenceForMessagesWithoutLowPart();
        //collectedConditionsForEquivalenceOfVisibleEvents = collectedConditionsForEquivalenceOfVisibleEvents.append(equivalenceForMessagesWithoutLowPart);
        return collectedConditionsForEquivalenceOfVisibleEvents;
    }
    
    public abstract ImmutableList<Term> equivalenceConditionsForLowlist(ImmutableList<Lowlist> lowlists);
    
    
    
    protected ImmutableList<Term> getFormulas(ImmutableList<Term> list) {
        ImmutableList<Term> formulas = ImmutableSLList.<Term>nil();
        for (Term term: list) {
            if (term.sort().equals(tb.tt().sort())) {
                formulas = formulas.append(term);
            }
        }
        return formulas;
    }
    
    protected ImmutableList<Term> withoutFormulas(ImmutableList<Term> list) {
        ImmutableList<Term> seq = ImmutableSLList.<Term>nil();
        for (Term term: list) {
            if (!term.sort().equals(tb.tt().sort())) {
                seq = seq.append(term);
            }
        }
        return seq;
    }
    
    protected ImmutableList<Term> getObjects(ImmutableList<Term> list) {
        Sort objectSort = services.getJavaInfo().objectSort();
        ImmutableList<Term> formulas = ImmutableSLList.<Term>nil();
        for (Term term: list) {
            if (term.sort().extendsTrans(objectSort)) {
                formulas = formulas.append(term);
            }
        }
        return formulas;
    }
    
    protected ImmutableList<Term> getBuiltInTypeExpressions(ImmutableList<Term> list) {
        Sort objectSort = (Sort) services.getNamespaces().sorts().lookup("java.lang.Object");
        ImmutableList<Term> formulas = ImmutableSLList.<Term>nil();
        for (Term term: list) {
            if (!(term.sort().extendsTrans(objectSort) || term.sort().equals(tb.tt().sort()))) {
                formulas = formulas.append(term);
            }
        }
        return formulas;
    }

}
