package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;

/* this is a class that applies UseAbstractContractRule 
* (rule using only abstract contracts without explicit pre-, postconditions, assignables)
*/
public class ContractAbstractRuleApp extends ContractRuleApp{

	ContractAbstractRuleApp(BuiltInRule rule, PosInOccurrence pio) {
		super(rule, pio);
	}
	
	@Override
    public UseOperationContractRule rule() {
    	return (UseAbstractOperationContractRule) builtInRule;
    }
	
	   @Override
	    public ContractRuleApp tryToInstantiate(Goal goal) {
	    	if (complete()) {
	    		return this;
	    	}
	    	Services services = goal.proof().getServices();
	    	ImmutableSet<FunctionalOperationContract> contracts = UseAbstractOperationContractRule
	    	        .getApplicableContracts(
	    	                UseAbstractOperationContractRule.computeInstantiation(
	    	                        posInOccurrence().subTerm(), services),
		                        services);
		if (contracts.size() !=1) return this; // incomplete app;
		Modality m = (Modality)programTerm().op();
		boolean transaction = (m == Modality.DIA_TRANSACTION || m == Modality.BOX_TRANSACTION);
		heapContext = HeapContext.getModHeaps(goal.proof().getServices(), transaction);
		return setContract(contracts.iterator().next());
	    }

	    @Override
	    public ContractRuleApp forceInstantiate(Goal goal) {
		if (complete()) {
			return this;
		}
		Services services = goal.proof().getServices();
		ImmutableSet<FunctionalOperationContract> contracts = UseAbstractOperationContractRule
		.getApplicableContracts(
				UseAbstractOperationContractRule.computeInstantiation(
						posInOccurrence().subTerm(), services),
						services);
		Modality m = (Modality)programTerm().op();
		boolean transaction = (m == Modality.DIA_TRANSACTION || m == Modality.BOX_TRANSACTION);
		heapContext = HeapContext.getModHeaps(goal.proof().getServices(), transaction);
		final FunctionalOperationContract combinedContract = services.getSpecificationRepository()
		.combineOperationContracts(contracts);
		return setContract(combinedContract);
	    }
	 
}
