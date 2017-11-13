package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;

public class CombinedClusterSpec extends AbstractDependencyClusterSpec {
    protected final KeYJavaType forClass;
    private final ImmutableList<String> specLabels;

    public CombinedClusterSpec(KeYJavaType forClass, String label, Services services, ImmutableList<String> specLabels) {
        super(label, services);
        this.specLabels = specLabels;
        this.forClass = forClass;
        
    }

    public ImmutableList<String> getSpecLabels() {
        return specLabels;
    }
    
    @Override
    public String toString() {
        return label + " combines " + specLabels;
    }

    @Override
    public ImmutableList<RewriteTaclet> getTaclets(Term self,
            InitConfig config) {
        ImmutableList<RewriteTaclet> taclets = ImmutableSLList.<RewriteTaclet>nil();
        
        for (String specLabel: specLabels) {
            DependencyClusterSpec spec = config.getServices().getSpecificationRepository().getDependencyClusterSpecByLabel(specLabel);
            taclets = taclets.prepend(spec.getTaclets(self, config));
        }
        
        taclets = taclets.prepend(eqivEventEqTaclet(self, config));
        taclets = taclets.prepend(eqivEventIsoTaclet(self, config));
        taclets = taclets.prepend(invEventTaclet(self, config));
        taclets = taclets.prepend(agreePreTaclet(self, config));
        taclets = taclets.prepend(agreePostTaclet(self, config));     
        
        
        return taclets;
    }

    //TODO JK move all this stuff in a factory class or something
    private RewriteTaclet eqivEventEqTaclet(Term self, InitConfig config) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        TermBuilder tb = config.getServices().getTermBuilder();
        
        final String name = "AAAAEquivEventEq" + label;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));
        
        Sort eventSort = services.getTypeConverter().getServiceEventLDT().eventSort();
        Term event1 = tb.var(SchemaVariableFactory.createTermSV(new Name("event1"), eventSort, false, false));
        Term event2 = tb.var(SchemaVariableFactory.createTermSV(new Name("event2"), eventSort, false, false));
        
        tacletBuilder.setFind(tb.func(getEquivEventEqPredicate(), event1, event2));
        
        ImmutableList<Term> terms = ImmutableSLList.<Term>nil();
        for (String specLabel: specLabels) {
            DependencyClusterSpec spec = config.getServices().getSpecificationRepository().getDependencyClusterSpecByLabel(specLabel);
            terms = terms.prepend(tb.func(spec.getEquivEventEqPredicate(), event1, event2));
        }
        
        tacletBuilder.addGoalTerm(tb.and(terms));
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)services.getNamespaces().ruleSets().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    private RewriteTaclet eqivEventIsoTaclet(Term self, InitConfig config) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        TermBuilder tb = config.getServices().getTermBuilder();
        
        final String name = "AAAAEquivEventIso" + label;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));
        
        Sort eventSort = services.getTypeConverter().getServiceEventLDT().eventSort();
        Term event1 = tb.var(SchemaVariableFactory.createTermSV(new Name("event1"), eventSort, false, false));
        Term event2 = tb.var(SchemaVariableFactory.createTermSV(new Name("event2"), eventSort, false, false));
        
        tacletBuilder.setFind(tb.func(getEquivEventIsoPredicate(), event1, event2));
        
        ImmutableList<Term> terms = ImmutableSLList.<Term>nil();
        for (String specLabel: specLabels) {
            DependencyClusterSpec spec = config.getServices().getSpecificationRepository().getDependencyClusterSpecByLabel(specLabel);
            terms = terms.prepend(tb.func(spec.getEquivEventIsoPredicate(), event1, event2));
        }
        
        tacletBuilder.addGoalTerm(tb.and(terms));
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)services.getNamespaces().ruleSets().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    private RewriteTaclet invEventTaclet(Term self, InitConfig config) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        TermBuilder tb = config.getServices().getTermBuilder();
        
        final String name = "AAAAInvEvent" + label;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));
        
        Sort eventSort = services.getTypeConverter().getServiceEventLDT().eventSort();
        Term event = tb.var(SchemaVariableFactory.createTermSV(new Name("event"), eventSort, false, false));
        
        tacletBuilder.setFind(tb.func(getVisibilityPredicate(), event));
        
        ImmutableList<Term> terms = ImmutableSLList.<Term>nil();
        for (String specLabel: specLabels) {
            DependencyClusterSpec spec = config.getServices().getSpecificationRepository().getDependencyClusterSpecByLabel(specLabel);
            terms = terms.prepend(tb.func(spec.getVisibilityPredicate(), event));
        }
        
        tacletBuilder.addGoalTerm(tb.and(terms));
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)services.getNamespaces().ruleSets().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    public RewriteTaclet agreePreTaclet(Term self, InitConfig config) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        TermBuilder tb = config.getServices().getTermBuilder();
        
        final String name = "AAAAAgreePre" + label;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));
        
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        Term heap1 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap1"), heapSort, false, false));
        Term heap2 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap2"), heapSort, false, false));
        
        tacletBuilder.setFind(tb.func(getAgreePrePredicate(), heap1, heap2));
        
        ImmutableList<Term> terms = ImmutableSLList.<Term>nil();
        for (String specLabel: specLabels) {
            DependencyClusterSpec spec = config.getServices().getSpecificationRepository().getDependencyClusterSpecByLabel(specLabel);
            terms = terms.prepend(tb.func(spec.getAgreePrePredicate(), heap1, heap2));
        }
        
        tacletBuilder.addGoalTerm(tb.and(terms));
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)services.getNamespaces().ruleSets().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    public RewriteTaclet agreePostTaclet(Term self, InitConfig config) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        TermBuilder tb = config.getServices().getTermBuilder();
        
        final String name = "AAAAAgreePost" + label;
        tacletBuilder.setDisplayName(name);
        tacletBuilder.setName(new Name(name));
        
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        Term heap1 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap1"), heapSort, false, false));
        Term heap2 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap2"), heapSort, false, false));
        
        tacletBuilder.setFind(tb.func(getAgreePostPredicate(), heap1, heap2));
        
        ImmutableList<Term> terms = ImmutableSLList.<Term>nil();
        for (String specLabel: specLabels) {
            DependencyClusterSpec spec = config.getServices().getSpecificationRepository().getDependencyClusterSpecByLabel(specLabel);
            terms = terms.prepend(tb.func(spec.getAgreePostPredicate(), heap1, heap2));
        }
        
        tacletBuilder.addGoalTerm(tb.and(terms));
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)services.getNamespaces().ruleSets().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }

    @Override
    public String getName() {
        return label;
    }

    @Override
    public String getDisplayName() {
        return label;
    }

    @Override
    public VisibilityModifier getVisibility() {
        // TODO JK stub
        System.out.println("asked for visibility");
        return null;
    }

    @Override
    public KeYJavaType getKJT() {
        return forClass;
    }

}
