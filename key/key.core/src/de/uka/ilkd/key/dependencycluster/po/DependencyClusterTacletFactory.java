package de.uka.ilkd.key.dependencycluster.po;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.ldt.TempEventLDT;
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

public class DependencyClusterTacletFactory {
    private final DependencyClusterContract contract;
    private final InitConfig proofConfig;
    private final TermBuilder tb;
    private final TempEventLDT ldt;
    private final IFProofObligationVars poVars;
    
    Term calltype1;
    Term calltype2;
    
    Term direction1;
    Term direction2;
    
    Term component1;
    Term component2;
    
    Term service1;
    Term service2;
    
    Term params1;
    Term params2;
    
    Term heap1;
    Term heap2;
    
    Term event1;
    Term event2;
    
    Term updatedParams1;
    Term updatedParams2;
    
    public DependencyClusterTacletFactory(DependencyClusterContract contract, InitConfig proofConfig, IFProofObligationVars poVars) {
        this.contract = contract;
        this.proofConfig = proofConfig;
        ldt = proofConfig.getServices().getTypeConverter().getTempEventLDT();
        
        tb = proofConfig.getServices().getTermBuilder();
        
        Sort calltypeSort = (Sort) proofConfig.getServices().getNamespaces().sorts().lookup("Calltype");
        Sort dirSort = (Sort) proofConfig.getServices().getNamespaces().sorts().lookup("CallDirection");
        Sort objectSort = (Sort) proofConfig.getServices().getNamespaces().sorts().lookup("java.lang.Object");
        Sort methodSort = (Sort) proofConfig.getServices().getNamespaces().sorts().lookup("Method");
        Sort seqSort = proofConfig.getServices().getTypeConverter().getSeqLDT().targetSort();
        Sort heapSort = proofConfig.getServices().getTypeConverter().getHeapLDT().targetSort();
        
        calltype1 = tb.var(SchemaVariableFactory.createTermSV(new Name("calltype1"), calltypeSort, false, false));
        calltype2 = tb.var(SchemaVariableFactory.createTermSV(new Name("calltype2"), calltypeSort, false, false));
        
        direction1 = tb.var(SchemaVariableFactory.createTermSV(new Name("direction1"), dirSort, false, false));
        direction2 = tb.var(SchemaVariableFactory.createTermSV(new Name("direction2"), dirSort, false, false));    
        
        component1 = tb.var(SchemaVariableFactory.createTermSV(new Name("component1"), objectSort, false, false));
        component2 = tb.var(SchemaVariableFactory.createTermSV(new Name("component2"), objectSort, false, false));
        
        service1 = tb.var(SchemaVariableFactory.createTermSV(new Name("service1"), methodSort, false, false));
        service2 = tb.var(SchemaVariableFactory.createTermSV(new Name("service2"), methodSort, false, false));
        
        params1 = tb.var(SchemaVariableFactory.createTermSV(new Name("params1"), seqSort, false, false));
        params2 = tb.var(SchemaVariableFactory.createTermSV(new Name("params2"), seqSort, false, false));
        
        heap1 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap1"), heapSort, false, false));
        heap2 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap2"), heapSort, false, false));
        
        event1 = tb.func(ldt.evConst(), calltype1, direction1, component1, service1, params1, heap1);
        event2 = tb.func(ldt.evConst(), calltype2, direction2, component2, service2, params2, heap2);
        
        updatedParams1 = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(ldt.getCurrentParams(), params1));
        updatedParams2 = tb.parallel(tb.elementary(tb.getBaseHeap(), heap2), tb.elementary(ldt.getCurrentParams(), params2));
        
        this.poVars = poVars;
    }
    
    public Term findTermEquivalence() {
        Term find = tb.func(ldt.equivEvent(), event1, event2);
        return find;
    }
    
    public Term bothEventsInvisible() {
        Term event1Invis = tb.func(ldt.invEvent(), event1);
        Term event2Invis = tb.func(ldt.invEvent(), event2);
        Term bothInvis = tb.and(event1Invis, event2Invis);
        return bothInvis;
    }
    
    public Term bothEventsVisible() {
        Term event1Vis = tb.not(tb.func(ldt.invEvent(), event1));
        Term event2Vis = tb.not(tb.func(ldt.invEvent(), event2));
        Term bothVis = tb.and(event1Vis, event2Vis);
        return bothVis;
    }
    
    public Term equalMetadata() {
        Term equalType = tb.equals(calltype1, calltype2);
        Term equalDirection = tb.equals(direction1, direction2);
        Term equalPartner = tb.equals(component1, component2);
        Term equalService = tb.equals(service1, service2);
        Term equalMetadata = tb.and(equalType, equalDirection, equalPartner, equalService);
        return equalMetadata;
    }
    
    public Term equivalenceForMessagesWithoutLowPart() {
        //TODO JK Do I still need this??? When are messages equivalent if they have no specified low parts in their content?
        ImmutableList<Term> collectedTerms = ImmutableSLList.<Term>nil();
        for (Lowlist list:contract.getSpecs().getLowIn().append(contract.getSpecs().getLowOut())) {
            Term specifiedCalltype;
            if (list.getCallType() == Lowlist.MessageType.CALL) {
                specifiedCalltype = tb.func(ldt.evCall());
            } else {
                specifiedCalltype = tb.func(ldt.evTerm());
            }
            Term specifiedDirection;
            if (list.getDirection() == Lowlist.Direction.IN) {
                specifiedDirection = tb.func(ldt.evIncoming());
            } else {
                specifiedDirection = tb.func(ldt.evOutgoing());
            }
            Term specifiedComponent = list.getCommunicationPartner().getTerm();
            Term updateHeapAndSelf = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(contract.getSelfVar(), poVars.c1.pre.self));
            Term updatedspecifiedComponent = tb.apply(updateHeapAndSelf, specifiedComponent);
            
            
            Term specifiedService = tb.func(ldt.getMethodIdentifier(list.getService().getMethodDeclaration(), proofConfig.getServices()));
            
            
            
            Term equalCalltypes1 = tb.equals(calltype1, specifiedCalltype);
            Term equalDirections1 = tb.equals(direction1, specifiedDirection);
            Term equalComponents1 = tb.equals(component1, updatedspecifiedComponent);
            Term equalServices1 = tb.equals(service1, specifiedService);
            Term message1fitsSpec = tb.and(equalCalltypes1, equalDirections1, equalComponents1, equalServices1);
            
            //We don't need that part since the messages have equal metadata here anyway
            /*
            Term equalCalltypes2 = tb.equals(calltype2, specifiedCalltype);
            Term equalDirections2 = tb.equals(direction2, specifiedDirection);
            Term equalComponents2 = tb.equals(component2, specifiedComponent);
            Term equalServices2 = tb.equals(service2, specifiedService);
            Term message2fitsSpec = tb.and(equalCalltypes2, equalDirections2, equalComponents2, equalServices2);
            
            Term atLeastOneFitsSpec = tb.or(message1fitsSpec, message2fitsSpec);
        
            Term messageEquivalenceNotRestrictedByThisList = tb.not(atLeastOneFitsSpec);
            */
            Term messageEquivalenceNotRestrictedByThisList = tb.not(message1fitsSpec);
            collectedTerms = collectedTerms.append(messageEquivalenceNotRestrictedByThisList);
        }
        return tb.and(collectedTerms);
    }
    
    public Term invisibilityForMessagesWithoutSpec() {
        ImmutableList<Term> collectedTerms = ImmutableSLList.<Term>nil();
        for (VisibilityCondition condition:contract.getSpecs().getVisible()) {
            Term specifiedCalltype;
            if (condition.getMessageType() == VisibilityCondition.MessageType.CALL) {
                specifiedCalltype = tb.func(ldt.evCall());
            } else {
                specifiedCalltype = tb.func(ldt.evTerm());
            }
            Term specifiedDirection;
            if (condition.getDirection() == VisibilityCondition.Direction.IN) {
                specifiedDirection = tb.func(ldt.evIncoming());
            } else {
                specifiedDirection = tb.func(ldt.evOutgoing());
            }
            Term specifiedComponent = condition.getCommunicationPartner().getTerm();
            Term updateHeapAndSelf = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(contract.getSelfVar(), poVars.c1.pre.self));
            Term updatedspecifiedComponent = tb.apply(updateHeapAndSelf, specifiedComponent);
            
            
            Term specifiedService = tb.func(ldt.getMethodIdentifier(condition.getServiceContext().getMethodDeclaration(), proofConfig.getServices()));
            
            
            
            Term equalCalltypes1 = tb.equals(calltype1, specifiedCalltype);
            Term equalDirections1 = tb.equals(direction1, specifiedDirection);
            Term equalComponents1 = tb.equals(component1, updatedspecifiedComponent);
            Term equalServices1 = tb.equals(service1, specifiedService);
            Term message1fitsSpec = tb.and(equalCalltypes1, equalDirections1, equalComponents1, equalServices1);
        
            Term messageInvisibilityNotRestrictedByThisCondition = tb.not(message1fitsSpec);
            collectedTerms = collectedTerms.append(messageInvisibilityNotRestrictedByThisCondition);
        }
        return tb.and(collectedTerms);
    }
    
    public Term equivalenceInVisibleCase() {
        Term visibleEquivalence = tb.and(bothEventsVisible(), equalMetadata(), tb.or(collectedConditionsForEquivalenceOfVisibleEvents()));
        return visibleEquivalence;
    }
    
    public Term replaceTermEquivalence() {
        Term replaceWith = tb.or(bothEventsInvisible(), equivalenceInVisibleCase());
        return replaceWith;
    }
    
    public RewriteTaclet getEventEquivalenceTaclet() {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        //TODO JK remove preceding As
        tacletBuilder.setDisplayName("AAAEquivEventDef");
        tacletBuilder.setName(new Name("AAAEquivEventDef"));
        
        tacletBuilder.setFind(findTermEquivalence());
        
        tacletBuilder.addGoalTerm(replaceTermEquivalence());
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)proofConfig.ruleSetNS().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    public RewriteTaclet getInvisibilityTaclet() {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        //TODO JK remove preceding As
        tacletBuilder.setDisplayName("AAAEventInvisibilityDef");
        tacletBuilder.setName(new Name("AAAEventInvisibilityDef"));

        tacletBuilder.setFind(findTermInvisibility());
        tacletBuilder.addGoalTerm(replaceTermInvisibility());
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)proofConfig.ruleSetNS().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        return taclet;
    }
    
    public Term replaceTermInvisibility() {
        return tb.or(tb.not(eventVisibleDueToExplicitSpec()), invisibilityForMessagesWithoutSpec());
    }

    public Term eventVisibleDueToExplicitSpec() {
        ImmutableList<Term> conditions = ImmutableSLList.<Term>nil();
        for (VisibilityCondition condition: contract.getSpecs().getVisible()) {

            Term checkDirection;
            if (condition.getDirection() == VisibilityCondition.Direction.IN){
                checkDirection = tb.func(ldt.evIncoming());
            } else {
                checkDirection = tb.func(ldt.evOutgoing());
            } 
                        
            Term checkCalltype;
            if (condition.getMessageType() == VisibilityCondition.MessageType.CALL) {
                checkCalltype = tb.func(ldt.evCall());
            } else {
                checkCalltype = tb.func(ldt.evTerm());
            }
            Term checkComponent = condition.getCommunicationPartner().getTerm();
            Term updateHeapAndSelf = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(contract.getSelfVar(), poVars.c1.pre.self));
            Term updatedCheckComponent = tb.apply(updateHeapAndSelf, checkComponent);
            
            Term checkService = tb.func(ldt.getMethodIdentifier(condition.getServiceContext().getMethodDeclaration(), proofConfig.getServices()));
            
            Term dirEq = tb.equals(direction1, checkDirection);
            Term typeEq = tb.equals(calltype1, checkCalltype);
            Term compEq = tb.equals(component1, updatedCheckComponent);
            Term servEq = tb.equals(service1, checkService);
            Term metadataFits = tb.and(dirEq, typeEq, compEq, servEq);

            conditions = conditions.append(tb.and(metadataFits, tb.apply(updatedParams1, tb.convertToFormula(condition.getTerm()))));
        }
        return tb.or(conditions);
    }

    public Term findTermInvisibility() {
        return tb.func(ldt.invEvent(), event1);
    }

    public ImmutableList<Term> collectedConditionsForEquivalenceOfVisibleEvents() {
        ImmutableList<Term> collectedConditionsForEquivalenceOfVisibleEvents = equivalenceConditionsForLowlist(contract.getSpecs().getLowIn());
        collectedConditionsForEquivalenceOfVisibleEvents = collectedConditionsForEquivalenceOfVisibleEvents.append(equivalenceConditionsForLowlist(contract.getSpecs().getLowOut()));
        
        Term equivalenceForMessagesWithoutLowPart = equivalenceForMessagesWithoutLowPart();
        collectedConditionsForEquivalenceOfVisibleEvents = collectedConditionsForEquivalenceOfVisibleEvents.append(equivalenceForMessagesWithoutLowPart);
        return collectedConditionsForEquivalenceOfVisibleEvents;
    }
    
    private ImmutableList<Term> equivalenceConditionsForLowlist(ImmutableList<Lowlist> lowlists) {
        ImmutableList<Term> collectedConditionsForEquivalenceOfVisibleEvents = ImmutableSLList.<Term>nil();
        for (Lowlist list: lowlists) {
            
            Term checkDirection;
            if (list.getDirection() == Lowlist.Direction.IN){
                checkDirection = tb.func(ldt.evIncoming());
            } else {
                checkDirection = tb.func(ldt.evOutgoing());
            } 
                        
            Term checkCalltype;
            if (list.getCallType() == Lowlist.MessageType.CALL) {
                checkCalltype = tb.func(ldt.evCall());
            } else {
                checkCalltype = tb.func(ldt.evTerm());
            }
            Term checkComponent = list.getCommunicationPartner().getTerm();
            Term updateHeapAndSelf = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(contract.getSelfVar(), poVars.c1.pre.self));
            Term updatedCheckComponent = tb.apply(updateHeapAndSelf, checkComponent);
            
            Term checkService = tb.func(ldt.getMethodIdentifier(list.getService().getMethodDeclaration(), proofConfig.getServices()));
            
            Term dirEq = tb.equals(direction1, checkDirection);
            Term typeEq = tb.equals(calltype1, checkCalltype);
            Term compEq = tb.equals(component1, updatedCheckComponent);
            Term servEq = tb.equals(service1, checkService);
            Term metadataFits = tb.and(dirEq, typeEq, compEq, servEq);

            ImmutableList<Term> expressionsEq = ImmutableSLList.<Term>nil();
            
            //Formulas
            for (Term term: getFormulas(list.getLowTerms())) {             
                //TODO JK Parser returns some "boolean" expressions (for example with > operator) as Formulas, not as expressions, so we need special treatment for those (can't be in sequences, dont have a = relation...)
                Term t1 = tb.apply(updatedParams1, term);
                Term t2 = tb.apply(updatedParams2, term);
                Term expressionComparison = tb.equals(t1, t2);

                expressionsEq = expressionsEq.append(expressionComparison);
            }
            
            //BuiltIn types
            if (!getBuiltInTypeExpressions(list.getLowTerms()).isEmpty()) {
                Term builtin = tb.seq(getBuiltInTypeExpressions(list.getLowTerms()));
                Term t1 = tb.apply(updatedParams1, builtin);
                Term t2 = tb.apply(updatedParams2, builtin);
                
                expressionsEq = expressionsEq.append(tb.equals(t1, t2));
            }
            
            //Objects
            if (!getObjects(list.getLowTerms()).isEmpty()) {
                Term objects = tb.seq(getObjects(list.getLowTerms()));
                Term t1 = tb.apply(updatedParams1, objects);
                Term t2 = tb.apply(updatedParams2, objects);
                
                Function objectsIsoFunction =
                        (Function)proofConfig.getServices().getNamespaces().functions().lookup("objectsIsomorphic");
                Function sameTypesFunction =
                        (Function)proofConfig.getServices().getNamespaces().functions().lookup("sameTypes");
                
                Term objectsIso = tb.func(objectsIsoFunction, t1, t1, t2, t2);
                Term sameTypes = tb.func(sameTypesFunction, t1, t2);
                
                expressionsEq = expressionsEq.append(tb.and(sameTypes, objectsIso));
            }

            
            if (!expressionsEq.isEmpty()) {
                collectedConditionsForEquivalenceOfVisibleEvents = collectedConditionsForEquivalenceOfVisibleEvents.append(tb.and(metadataFits, tb.and(expressionsEq)));
            }
        }
        return collectedConditionsForEquivalenceOfVisibleEvents;
    }
    
    private ImmutableList<Term> getFormulas(ImmutableList<Term> list) {
        ImmutableList<Term> formulas = ImmutableSLList.<Term>nil();
        for (Term term: list) {
            if (term.sort().equals(tb.tt().sort())) {
                formulas = formulas.append(term);
            }
        }
        return formulas;
    }
    
    private ImmutableList<Term> getObjects(ImmutableList<Term> list) {
        Sort objectSort = proofConfig.getServices().getJavaInfo().objectSort();
        ImmutableList<Term> formulas = ImmutableSLList.<Term>nil();
        for (Term term: list) {
            if (term.sort().extendsTrans(objectSort)) {
                formulas = formulas.append(term);
            }
        }
        return formulas;
    }
    
    private ImmutableList<Term> getBuiltInTypeExpressions(ImmutableList<Term> list) {
        Sort objectSort = (Sort) proofConfig.getServices().getNamespaces().sorts().lookup("java.lang.Object");
        ImmutableList<Term> formulas = ImmutableSLList.<Term>nil();
        for (Term term: list) {
            if (!(term.sort().extendsTrans(objectSort) || term.sort().equals(tb.tt().sort()))) {
                formulas = formulas.append(term);
            }
        }
        return formulas;
    }

}
