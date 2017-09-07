package de.uka.ilkd.key.dependencycluster.po;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.ClusterSatisfactionContract;
import de.uka.ilkd.key.util.DependencyClusterSpec;
import de.uka.ilkd.key.util.Lowlist;
import de.uka.ilkd.key.util.VisibilityCondition;

public class EventEquivalenceWithEqFactory
        extends EventEquivalenceTacletFactory {

    private final Term self;


    public EventEquivalenceWithEqFactory(DependencyClusterSpec localSpec, Term self,
            InitConfig config, Function equivEventFunction, Function invEventFunction, String ruleNameSuffix) {
        super(config, localSpec.getLowIn(), localSpec.getLowOut(), localSpec.getVisible(), equivEventFunction, invEventFunction, ruleNameSuffix);
        
        this.self = self;
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

            Term messageEquivalenceNotRestrictedByThisList = tb.not(message1fitsSpec);
            collectedTerms = collectedTerms.append(messageEquivalenceNotRestrictedByThisList);
        }
        return tb.and(collectedTerms);
    }
    
    @Override
    public Term invisibilityForMessagesWithoutSpec() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term eventVisibleDueToExplicitSpec() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableList<Term> equivalenceConditionsForLowlist(
            ImmutableList<Lowlist> lowlists) {
        // TODO Auto-generated method stub
        return null;
    }

}
