package smt;

import java.util.List;

import org.key_project.util.collection.ImmutableList;

import api.key.KeYAPI;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.Contract;
import prover.CounterExample;
import prover.InvGenResult;
import prover.Invariant;
import prover.ProofResult;
import prover.ProofWrapper;
import prover.SequentWrapper;

public class Main {

	private static String benchmarksFile1 = "benchmarks/Loop1/Loop1.java";
	private static KeYAPI keyAPI;
	
	public static void main(String[] args) {
		keyAPI = new KeYAPI(benchmarksFile1);
		List<Contract> proofContracts = keyAPI.getContracts();
		ProofResult result = null;
		for(Contract currentContract : proofContracts) {
			Proof currentProof = keyAPI.createProof(currentContract);
			result = attemptProve(currentProof);
		}
		if(result != null) System.out.println(result);
	}
	
	private static ProofResult attemptProve(Proof proof) {
		while(!keyAPI.isClosed(proof)) {
			ImmutableList<Goal> openGoals = keyAPI.prove(proof);
			for(Goal currentGoal : openGoals) {
				SequentWrapper currentSequent = keyAPI.getSequent(currentGoal);
				InvGenResult result = attemptInvGen(currentSequent, proof);
				if(result instanceof CounterExample) {
					CounterExample counterexample = (CounterExample)result;
					return counterexample;
				} else {
					Invariant invariant = (Invariant)result;
					keyAPI.applyInvariantRule(currentGoal, invariant);
					attemptProve(proof);
				}
			}
		}
		return new ProofWrapper(proof); 
	}
	
	public static InvGenResult attemptInvGen(SequentWrapper sequent, Proof proof) {
		ProblemFactory.create(proof);
		
		List<Term> gamma 		= sequent.getGamma();
		StatementBlock program 	= sequent.getProgram();
		Term phi 				= sequent.getPhi();
		While loop 				= sequent.getLoop();
		Term update				= sequent.getUpdate();
		
		Term suggestedInvariant	= keyAPI.getSuggestedInvariant(loop);
		return new Invariant(suggestedInvariant);
	}
	
}
