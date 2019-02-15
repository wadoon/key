package api.key;

import java.io.File;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;
import prover.Invariant;
import prover.SequentWrapper;

public class KeYAPI {
	//TODO:Daniel private modifier
	public KeYEnvironment<?> myEnvironment = null;
	
	public KeYAPI(String fileName) {
		File location = new File(fileName);
		try {
			// Ensure that Taclets are parsed
			if (!ProofSettings.isChoiceSettingInitialised()) {
				myEnvironment = KeYEnvironment.load(location, null, null, null);
				myEnvironment.dispose();
			}
			// Set Taclet options
			ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
			HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
			HashMap<String, String> newSettings = new HashMap<String, String>(oldSettings);
			newSettings.putAll(MiscTools.getDefaultTacletOptions());
			newSettings.put("LOOP_OPTIONS_KEY", "NONE");
			choiceSettings.setDefaultChoices(newSettings);
			// Load source code
			myEnvironment = KeYEnvironment.load(location, null, null, null);
		} catch (ProblemLoaderException e) {
			e.printStackTrace();
		}
	}

	public List<Contract> getContracts() {
		List<Contract> proofContracts = new LinkedList<Contract>();
		Set<KeYJavaType> kjts = myEnvironment.getJavaInfo().getAllKeYJavaTypes();
		for (KeYJavaType type : kjts) {
			if (!KeYTypeUtil.isLibraryClass(type)) {
				ImmutableSet<IObserverFunction> targets = myEnvironment.getSpecificationRepository()
						.getContractTargets(type);
				for (IObserverFunction target : targets) {
					ImmutableSet<Contract> contracts = myEnvironment.getSpecificationRepository().getContracts(type,
							target);
					for (Contract contract : contracts) {
						proofContracts.add(contract);
					}
				}
			}
		}
		return proofContracts;
	}
	
	public Proof createProof(Contract contract) {
		Proof proof = null;
		try {
			proof = myEnvironment.createProof(contract.createProofObl(myEnvironment.getInitConfig(), contract));
		} catch (ProofInputException e) {
			e.printStackTrace();
		}
		return proof;
	}
	
	public ImmutableList<Goal> prove(Proof proof) {
		StrategyProperties strategyProperties = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
		strategyProperties.setProperty(StrategyProperties.DEP_OPTIONS_KEY, 				StrategyProperties.DEP_ON);
		strategyProperties.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, 			StrategyProperties.LOOP_NONE);
		strategyProperties.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, 			StrategyProperties.METHOD_CONTRACT);
		strategyProperties.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, 	StrategyProperties.NON_LIN_ARITH_DEF_OPS);
		strategyProperties.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, 			StrategyProperties.QUERY_ON);
		strategyProperties.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, 		StrategyProperties.STOPMODE_DEFAULT);
		int maxSteps = 10000;
		ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
		ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(strategyProperties);
		proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
		proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, strategyProperties));
		myEnvironment.getUi().getProofControl().startAndWaitForAutoMode(proof);
		return proof.openGoals();
	}
	
	public SequentWrapper getSequent(Goal goal) {
		return new SequentWrapper(goal.sequent(),myEnvironment.getServices().getTermBuilder());
	}
	
	public boolean isClosed(Proof proof) {
		return (proof.openGoals().isEmpty());
	}
	
	public Term getSuggestedInvariant(While whileStatement) {
		LoopSpecification loopSpecification = myEnvironment.getServices().getSpecificationRepository().getLoopSpec(whileStatement);
		Term loopInvariant = loopSpecification.getInvariant(myEnvironment.getServices());
		return loopInvariant;
	}
	
	public void applyInvariantRule(Goal goal, Invariant invariant) {
		WhileInvariantRule invariantRule = WhileInvariantRule.INSTANCE;
		PosInOccurrence poi = new PosInOccurrence(goal.sequent().succedent().get(1), PosInTerm.getTopLevel(), false);
		TermServices services = myEnvironment.getServices();
		LoopInvariantBuiltInRuleApp ruleApplication = new LoopInvariantBuiltInRuleApp(invariantRule, poi, services);
		ruleApplication = ruleApplication.tryToInstantiate(goal);
		LoopSpecification spec = ruleApplication.getSpec();
		Services serv = goal.proof().getServices();
		
		Map<LocationVariable, Term> invariants = new HashMap<>();
		TermBuilder termBuilder = services.getTermBuilder();
		Map<LocationVariable, Term> freeInvariants = new HashMap<>();
		Map<LocationVariable, Term> modifies = /*new HashMap<>();//*/spec.getInternalModifies();
		Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs = spec.getInternalInfFlowSpec();
		Term variant = null;
		
		Term update = ruleApplication.posInOccurrence().sequentFormula().formula().sub(0);
		Term termInv = invariant.getFormula();
		Term loopInvariant = termInv;
		
		LocationVariable baseHeap  = serv.getTypeConverter().getHeapLDT().getHeap();
		LocationVariable savedHeap = serv.getTypeConverter().getHeapLDT().getSavedHeap();
		invariants.put(baseHeap, loopInvariant);
		spec = spec.configurate(invariants, freeInvariants, modifies, infFlowSpecs, variant);
		
		
		ruleApplication.setLoopInvariant(spec);
		goal.apply(ruleApplication);
	}

}
