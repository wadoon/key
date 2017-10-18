package de.uka.ilkd.key.dependencycluster.po;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.ClusterSatisfactionContract;
import de.uka.ilkd.key.speclang.ComponentCluster;
import de.uka.ilkd.key.speclang.ServiceDependencyClusterSpec;
import de.uka.ilkd.key.util.Lowlist;
import de.uka.ilkd.key.util.VisibilityCondition;

public class EventEquivalenceWithEqFactory
        extends EventEquivalenceTacletFactory {

    private final Term self;


    public EventEquivalenceWithEqFactory(ServiceDependencyClusterSpec localSpec, Term self,
            InitConfig config, Function equivEventFunction, Function invEventFunction, String ruleNameSuffix) {
        super(config, localSpec.getLowIn(), localSpec.getLowOut(), localSpec.getVisible(), equivEventFunction, invEventFunction, ruleNameSuffix);
        
        this.self = self;
    }

    public EventEquivalenceWithEqFactory(ComponentCluster globalSpec, Term self,
            InitConfig config, Function equivEventFunction, Function invEventFunction, String ruleNameSuffix) {
        super(config, globalSpec.getLowIn(), globalSpec.getLowOut(), globalSpec.getVisible(), equivEventFunction, invEventFunction, ruleNameSuffix);
        this.self = self;
    }

    //TODO JK terms for equivalenceForMessagesWithoutLowPart and invisibilityForMessagesWithoutSpec and eventVisibleDueToExplicitSpec probably don't need to be overriden if done properly
    @Override
    public Term equivalenceForMessagesWithoutLowPart() {
        //TODO JK Do I still need this??? When are messages equivalent if they have no specified low parts in their content?
        ImmutableList<Term> collectedTerms = ImmutableSLList.<Term>nil();
        for (Lowlist list:lowIn.append(lowOut)) {
            Term specifiedCalltype;
            Term specifiedCaller;
            Term specifiedCallee;
            if (list.getCallType() == Lowlist.MessageType.CALL) {
                specifiedCalltype = tb.evCall();
                specifiedCaller = tb.getEnvironmentCaller();
                specifiedCallee = self; //TODO JK is this a proper self var for this purpose?
            } else {
                specifiedCalltype = tb.evTerm();
                specifiedCaller = self;
                specifiedCallee = list.getCommunicationPartner().getTerm();
            }

            //TODO JK maybe we have to update heap here as well... I really need to wrap my head around which self vars are used where...
            Term updateHeap = tb.elementary(tb.getBaseHeap(), heap1);
            Term updatedSpecifiedCaller = tb.apply(updateHeap, specifiedCaller);
            Term updatedSpecifiedCallee = tb.apply(updateHeap, specifiedCallee);
                        
            Term specifiedService = tb.func(ldt.getMethodIdentifierByDeclaration(list.getService().getMethodDeclaration(), proofConfig.getServices()));
            
            
            
            Term equalCalltypes1 = tb.equals(calltype1, specifiedCalltype);
            Term equalCallers1 = tb.equals(caller1, updatedSpecifiedCaller);
            Term equalCallees1 = tb.equals(callee1, updatedSpecifiedCallee);
            Term equalServices1 = tb.equals(service1, specifiedService);
            Term message1fitsSpec = tb.and(equalCalltypes1, equalCallers1, equalCallees1, equalServices1);

            Term messageEquivalenceNotRestrictedByThisList = tb.not(message1fitsSpec);
            collectedTerms = collectedTerms.append(messageEquivalenceNotRestrictedByThisList);
        }
        return tb.and(collectedTerms);
    }
    
    @Override
    public Term invisibilityForMessagesWithoutSpec() {
        ImmutableList<Term> collectedTerms = ImmutableSLList.<Term>nil();
        for (VisibilityCondition condition:visible) {
            Term specifiedCalltype;
            Term specifiedCaller;
            Term specifiedCallee;
            if (condition.getMessageType() == VisibilityCondition.MessageType.CALL) {
                specifiedCalltype = tb.evCall();
                if (condition.getDirection() == VisibilityCondition.Direction.IN) {
                    specifiedCaller = tb.getEnvironmentCaller();
                    specifiedCallee = self;
                } else {
                    specifiedCaller = self;
                    specifiedCallee = condition.getCommunicationPartner().getTerm();
                }
            } else {
                specifiedCalltype = tb.evTerm();
                if (condition.getDirection() == VisibilityCondition.Direction.OUT) {
                    specifiedCaller = tb.getEnvironmentCaller();
                    specifiedCallee = self;
                } else {
                    specifiedCaller = self;
                    specifiedCallee = condition.getCommunicationPartner().getTerm();
                }
            }
            
            Term updateHeap = tb.elementary(tb.getBaseHeap(), heap1);
            Term updatedSpecifiedCaller = tb.apply(updateHeap, specifiedCaller);
            Term updatedSpecifiedCallee = tb.apply(updateHeap, specifiedCallee);
                        
            Term specifiedService = tb.func(ldt.getMethodIdentifierByDeclaration(condition.getServiceContext().getMethodDeclaration(), proofConfig.getServices()));
                      
            Term equalCalltypes1 = tb.equals(calltype1, specifiedCalltype);
            Term equalCallers1 = tb.equals(caller1, updatedSpecifiedCaller);
            Term equalCallees1 = tb.equals(callee1, updatedSpecifiedCallee);
            Term equalServices1 = tb.equals(service1, specifiedService);
            Term message1fitsSpec = tb.and(equalCalltypes1, equalCallers1, equalCallees1, equalServices1);
        
            Term messageInvisibilityNotRestrictedByThisCondition = tb.not(message1fitsSpec);
            collectedTerms = collectedTerms.append(messageInvisibilityNotRestrictedByThisCondition);
        }
        return tb.and(collectedTerms);
    }

    @Override
    public Term eventVisibleDueToExplicitSpec() {
        ImmutableList<Term> conditions = ImmutableSLList.<Term>nil();
        for (VisibilityCondition condition: visible) {

            Term specifiedCalltype;
            Term specifiedCaller;
            Term specifiedCallee;
            if (condition.getMessageType() == VisibilityCondition.MessageType.CALL) {
                specifiedCalltype = tb.evCall();
                if (condition.getDirection() == VisibilityCondition.Direction.IN){
                    specifiedCaller = tb.getEnvironmentCaller();
                    specifiedCallee = self;
                } else {
                    specifiedCaller = self;
                    specifiedCallee = condition.getCommunicationPartner().getTerm();
                } 
            } else {
                specifiedCalltype = tb.evTerm();
                if (condition.getDirection() == VisibilityCondition.Direction.OUT){
                    specifiedCaller = tb.getEnvironmentCaller();
                    specifiedCallee = self;
                } else {
                    specifiedCaller = self;
                    specifiedCallee = condition.getCommunicationPartner().getTerm();
                } 
            }
            Term updateHeap = tb.elementary(tb.getBaseHeap(), heap1);
            Term updatedSpecifiedCaller = tb.apply(updateHeap, specifiedCaller);
            Term updatedSpecifiedCallee = tb.apply(updateHeap, specifiedCallee);
            
            Term specifiedService = tb.func(ldt.getMethodIdentifierByDeclaration(condition.getServiceContext().getMethodDeclaration(), proofConfig.getServices()));

            Term equalCalltypes1 = tb.equals(calltype1, specifiedCalltype);
            Term equalCallers1 = tb.equals(caller1, updatedSpecifiedCaller);
            Term equalCallees1 = tb.equals(callee1, updatedSpecifiedCallee);
            Term equalServices1 = tb.equals(service1, specifiedService);
            Term message1fitsSpec = tb.and(equalCalltypes1, equalCallers1, equalCallees1, equalServices1);
            conditions = conditions.append(tb.and(message1fitsSpec, tb.apply(updatedParams1, tb.convertToFormula(condition.getTerm()))));
        }
        return tb.or(conditions);
    }

    @Override
    public ImmutableList<Term> equivalenceConditionsForLowlist(
            ImmutableList<Lowlist> lowlists) {
        ImmutableList<Term> collectedConditionsForEquivalenceOfVisibleEvents = ImmutableSLList.<Term>nil();
        for (Lowlist list: lowlists) {
            Term specifiedCalltype;
            Term specifiedCaller;
            Term specifiedCallee;
            if (list.getCallType() == Lowlist.MessageType.CALL) {
                specifiedCalltype = tb.evCall();
                specifiedCaller = tb.getEnvironmentCaller();
                specifiedCallee = self; //TODO JK is this a proper self var for this purpose?
            } else {
                specifiedCalltype = tb.evTerm();
                specifiedCaller = self;
                specifiedCallee = list.getCommunicationPartner().getTerm();
            }

            Term updateHeap = tb.elementary(tb.getBaseHeap(), heap1);
            Term updatedSpecifiedCaller = tb.apply(updateHeap, specifiedCaller);
            Term updatedSpecifiedCallee = tb.apply(updateHeap, specifiedCallee);
                        
            Term specifiedService = tb.func(ldt.getMethodIdentifierByDeclaration(list.getService().getMethodDeclaration(), proofConfig.getServices()));
               
            Term equalCalltypes1 = tb.equals(calltype1, specifiedCalltype);
            Term equalCallers1 = tb.equals(caller1, updatedSpecifiedCaller);
            Term equalCallees1 = tb.equals(callee1, updatedSpecifiedCallee);
            Term equalServices1 = tb.equals(service1, specifiedService);
            Term message1fitsSpec = tb.and(equalCalltypes1, equalCallers1, equalCallees1, equalServices1);

            ImmutableList<Term> expressionsEq = ImmutableSLList.<Term>nil();
            
            //TODO JK here is the only real difference to the version with isomorphisms, try better code reuse
            for (Term term: list.getLowTerms()) {             
                Term t1 = tb.apply(updatedParams1, term);
                Term t2 = tb.apply(updatedParams2, term);
                Term expressionComparison = tb.equals(t1, t2);
                
                expressionsEq = expressionsEq.append(expressionComparison);
            }
            
            if (!expressionsEq.isEmpty()) {
                collectedConditionsForEquivalenceOfVisibleEvents = 
                        collectedConditionsForEquivalenceOfVisibleEvents.append(tb.imp(message1fitsSpec, tb.and(expressionsEq)));
            }
        }
        return collectedConditionsForEquivalenceOfVisibleEvents;
    }

}
