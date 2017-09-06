package de.uka.ilkd.key.dependencycluster.po;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.util.Lowlist;
import de.uka.ilkd.key.util.VisibilityCondition;

public class EventEquivalenceWithIsoFactory
        extends EventEquivalenceTacletFactory {
    
    private final DependencyClusterContract contract;
    private final IFProofObligationVars poVars;

    public EventEquivalenceWithIsoFactory(DependencyClusterContract contract,
            InitConfig proofConfig, IFProofObligationVars poVars) {
        super(proofConfig, contract.getSpecs().getLowIn(), contract.getSpecs().getLowOut(), contract.getSpecs().getVisible());
        
        this.contract = contract;

        this.poVars = poVars;
    }
    
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
                specifiedCallee = poVars.c1.pre.self; //TODO JK is this a proper self var for this purpose?
            } else {
                specifiedCalltype = tb.evTerm();
                specifiedCaller = poVars.c1.pre.self;
                specifiedCallee = list.getCommunicationPartner().getTerm();
            }

            Term updateHeapAndSelf = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(contract.getSelfVar(), poVars.c1.pre.self));
            Term updatedSpecifiedCaller = tb.apply(updateHeapAndSelf, specifiedCaller);
            Term updatedSpecifiedCallee = tb.apply(updateHeapAndSelf, specifiedCallee);
                        
            Term specifiedService = tb.func(ldt.getMethodIdentifierByDeclaration(list.getService().getMethodDeclaration(), proofConfig.getServices()));
            
            
            
            Term equalCalltypes1 = tb.equals(calltype1, specifiedCalltype);
            Term equalCallers1 = tb.equals(caller1, updatedSpecifiedCaller);
            Term equalCallees1 = tb.equals(callee1, updatedSpecifiedCallee);
            Term equalServices1 = tb.equals(service1, specifiedService);
            Term message1fitsSpec = tb.and(equalCalltypes1, equalCallers1, equalCallees1, equalServices1);
            
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
                    specifiedCallee = poVars.c1.pre.self;
                } else {
                    specifiedCaller = poVars.c1.pre.self;
                    specifiedCallee = condition.getCommunicationPartner().getTerm();
                }
            } else {
                specifiedCalltype = tb.evTerm();
                if (condition.getDirection() == VisibilityCondition.Direction.OUT) {
                    specifiedCaller = tb.getEnvironmentCaller();
                    specifiedCallee = poVars.c1.pre.self;
                } else {
                    specifiedCaller = poVars.c1.pre.self;
                    specifiedCallee = condition.getCommunicationPartner().getTerm();
                }
            }
            
            Term updateHeapAndSelf = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(contract.getSelfVar(), poVars.c1.pre.self));
            Term updatedSpecifiedCaller = tb.apply(updateHeapAndSelf, specifiedCaller);
            Term updatedSpecifiedCallee = tb.apply(updateHeapAndSelf, specifiedCallee);
                        
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
                    specifiedCallee = poVars.c1.pre.self;
                } else {
                    specifiedCaller = poVars.c1.pre.self;
                    specifiedCallee = condition.getCommunicationPartner().getTerm();
                } 
            } else {
                specifiedCalltype = tb.evTerm();
                if (condition.getDirection() == VisibilityCondition.Direction.OUT){
                    specifiedCaller = tb.getEnvironmentCaller();
                    specifiedCallee = poVars.c1.pre.self;
                } else {
                    specifiedCaller = poVars.c1.pre.self;
                    specifiedCallee = condition.getCommunicationPartner().getTerm();
                } 
            }
            Term updateHeapAndSelf = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(contract.getSelfVar(), poVars.c1.pre.self));
            Term updatedSpecifiedCaller = tb.apply(updateHeapAndSelf, specifiedCaller);
            Term updatedSpecifiedCallee = tb.apply(updateHeapAndSelf, specifiedCallee);
            
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
    
    public ImmutableList<Term> equivalenceConditionsForLowlist(ImmutableList<Lowlist> lowlists) {
        ImmutableList<Term> collectedConditionsForEquivalenceOfVisibleEvents = ImmutableSLList.<Term>nil();
        for (Lowlist list: lowlists) {
            Term specifiedCalltype;
            Term specifiedCaller;
            Term specifiedCallee;
            if (list.getCallType() == Lowlist.MessageType.CALL) {
                specifiedCalltype = tb.evCall();
                specifiedCaller = tb.getEnvironmentCaller();
                specifiedCallee = poVars.c1.pre.self; //TODO JK is this a proper self var for this purpose?
            } else {
                specifiedCalltype = tb.evTerm();
                specifiedCaller = poVars.c1.pre.self;
                specifiedCallee = list.getCommunicationPartner().getTerm();
            }

            Term updateHeapAndSelf = tb.parallel(tb.elementary(tb.getBaseHeap(), heap1), tb.elementary(contract.getSelfVar(), poVars.c1.pre.self));
            Term updatedSpecifiedCaller = tb.apply(updateHeapAndSelf, specifiedCaller);
            Term updatedSpecifiedCallee = tb.apply(updateHeapAndSelf, specifiedCallee);
                        
            Term specifiedService = tb.func(ldt.getMethodIdentifierByDeclaration(list.getService().getMethodDeclaration(), proofConfig.getServices()));
               
            Term equalCalltypes1 = tb.equals(calltype1, specifiedCalltype);
            Term equalCallers1 = tb.equals(caller1, updatedSpecifiedCaller);
            Term equalCallees1 = tb.equals(callee1, updatedSpecifiedCallee);
            Term equalServices1 = tb.equals(service1, specifiedService);
            Term message1fitsSpec = tb.and(equalCalltypes1, equalCallers1, equalCallees1, equalServices1);

            ImmutableList<Term> expressionsEq = ImmutableSLList.<Term>nil();
            
            
            //TODO JK handle sequences with objects CURRENTLY UNSOUND bc isomorphy doesn't include them! check sequence stuff in general
            //Formulas
            for (Term term: getFormulas(list.getLowTerms())) {             
                //TODO JK Parser returns some "boolean" expressions (for example with > operator) as Formulas, not as expressions, so we need special treatment for those (can't be in sequences, dont have a = relation...)
                Term t1 = tb.apply(updatedParams1, term);
                Term t2 = tb.apply(updatedParams2, term);
                Term expressionComparison = tb.equals(t1, t2);

                expressionsEq = expressionsEq.append(expressionComparison);
            }
            
            //BuiltIn types
            for (Term term: getBuiltInTypeExpressions(list.getLowTerms())) {
                Term t1 = tb.apply(updatedParams1, term);
                Term t2 = tb.apply(updatedParams2, term);
                Term expressionComparison = tb.equals(t1, t2);
                
                expressionsEq = expressionsEq.append(expressionComparison);
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
                collectedConditionsForEquivalenceOfVisibleEvents = 
                        collectedConditionsForEquivalenceOfVisibleEvents.append(tb.and(message1fitsSpec, tb.and(expressionsEq)));
            }
        }
        return collectedConditionsForEquivalenceOfVisibleEvents;
    }

}
