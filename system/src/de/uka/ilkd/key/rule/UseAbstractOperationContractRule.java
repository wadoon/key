package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;

import de.uka.ilkd.key.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;

import de.uka.ilkd.key.speclang.FunctionalOperationContract;


/*
 * Compared to UseOperationContractRule this rule only allows 
 * the usage of abstractly defined contracts, to ensure later reuse of proofs.
 * Application of this rule is defined in the class ContractAbstractRuleApp
 */
public class UseAbstractOperationContractRule extends UseOperationContractRule implements BuiltInRule {

	public static final UseAbstractOperationContractRule INSTANCE = new UseAbstractOperationContractRule();

	private static final Name NAME = new Name("Use Abstract Operation Contract");


	// -------------------------------------------------------------------------
	// constructors
	// -------------------------------------------------------------------------

	private UseAbstractOperationContractRule() {
	}
	
	public static ImmutableSet<FunctionalOperationContract> getApplicableContracts(
			Instantiation inst, Services services) {

		if (inst == null) {
			return DefaultImmutableSet.<FunctionalOperationContract> nil();
		}

		// there must be applicable contracts for the operation
		return getApplicableContracts(services, inst.pm, inst.staticType,
				inst.mod);

	}

	/**
	 * Returns the operation contracts which are applicable for the passed
	 * operation and the passed modality
	 */
	private static ImmutableSet<FunctionalOperationContract> getApplicableContracts(
			Services services, IProgramMethod pm, KeYJavaType kjt,
			Modality modality) {

		ImmutableSet<FunctionalOperationContract> allContracts = services
				.getSpecificationRepository().getOperationContracts(kjt, pm,
						modality);
		ImmutableSet<FunctionalOperationContract> result = DefaultImmutableSet
				.<FunctionalOperationContract> nil();

		for (FunctionalOperationContract contract : allContracts) {
			if (contract.isAbstract()) {
				result = result.add(contract);
			}
		}

		// in box modalities, diamond contracts may be applied as well
		if (modality == Modality.BOX) {
			result = result.union(services.getSpecificationRepository()
					.getOperationContracts(kjt, pm, Modality.DIA));
		} else if (modality == Modality.BOX_TRANSACTION) {
			result = result.union(services.getSpecificationRepository()
					.getOperationContracts(kjt, pm, Modality.DIA_TRANSACTION));
		}

		return result;
	}

	// -------------------------------------------------------------------------
	// public interface
	// -------------------------------------------------------------------------

	@Override
	public Name name() {
		return NAME;
	}

	@Override
	public String displayName() {
		return NAME.toString();
	}

	@Override
	public String toString() {
		return displayName();
	}

	// -------------------------------------------------------------------------
	// inner classes
	// -------------------------------------------------------------------------

	@Override
	public ContractRuleApp createApp(PosInOccurrence pos) {
		return new ContractAbstractRuleApp(this, pos);
	}
}
