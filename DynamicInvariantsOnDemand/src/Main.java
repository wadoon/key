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

	private static String benchmarksFile = "benchmarks/Cohen.java";
	private static KeYAPI keyAPI;
	
	public static void main(String[] args) {
		keyAPI = new KeYAPI(benchmarksFile);
		List<Contract> proofContracts = keyAPI.getContracts(); // Kopf von Cohen, public normal_behavior @ requires (0 <= x) && (0 < y); @ ensures \result*y <= x && x <= (\result+1)*y;
		for(Contract currentContract : proofContracts) {
			Proof currentProof = keyAPI.createProof(currentContract); // Contract nochmal umgeschrieben (in Taclet?)
			ProofResult result = attemptProve(currentProof);
		}
		System.out.println("done");
	}
	
	private static ProofResult attemptProve(Proof proof) {
		while(!keyAPI.isClosed(proof)) {
			ImmutableList<Goal> openGoals = keyAPI.prove(proof); // erstes Goal ist komplettes Cohen Programm
			for(Goal currentGoal : openGoals) {
				SequentWrapper currentSequent = keyAPI.getSequent(currentGoal);
				InvGenResult result = attemptInvGen(currentSequent);
				if(result instanceof CounterExample) {
					CounterExample counterexample = (CounterExample)result;
					return counterexample;
				} else {
					Invariant invariant = (Invariant)result;
					keyAPI.applyInvariantRule(currentGoal, invariant);
					attemptProve(proof); //!!! Rekursiv. Beim ersten Durchlauf bis hier: Invariant für Loop 1 angewendet. Dadurch beim nächsten attemptProve, openGoal mit "abgerollter"/gelöster 1. Schleife
				}
			}
		}
		return new ProofWrapper(proof);
	}
	
	public static InvGenResult attemptInvGen(SequentWrapper sequent) {
		List<Term> gamma 		= sequent.getGamma();   // [wellFormed(heap), equals(boolean::select(heap,self,java.lang.Object::<created>),TRUE), equals(SimpleExamples::exactInstance(self),TRUE), measuredByEmpty, geq(x,Z(0(#))), geq(y,Z(1(#))), not(equals(self,null))]
		StatementBlock program 	= sequent.getProgram(); // {while ( _y<=r ) {     int a = 1;     int b = _y;                         while ( 2*b<=r ) {       a=2*a;       b=2*b;     }     r=r-b;     q=q+a;   }                 return  q; }
		Term phi 				= sequent.getPhi();		// Cohen Kopf: and(and(and(leq(mul(y,result),x),geq(mul(y,result),add(x,mul(y,Z(neglit(1(#)))))))<<SC>>,java.lang.Object::<inv>(heap,self)<<impl>>)<<SC>>,equals(exc,null)<<impl>>)
		While loop 				= sequent.getLoop();	// while ( _y<=r ) {   int a = 1;   int b = _y;                         while ( 2*b<=r ) {     a=2*a;     b=2*b;   }   r=r-b;   q=q+a; }
		Term update				= sequent.getUpdate();  // parallel-upd(parallel-upd(parallel-upd(parallel-upd(elem-update(_x)(x),elem-update(_y)(y)),elem-update(exc)(null)),elem-update(q)(Z(0(#)))),elem-update(r)(x))
		Term suggestedInvariant	= keyAPI.getSuggestedInvariant(loop); // Erste (User angegebene) Loop Invariante: and(leq(Z(0(#)),r),equals(_x,javaAddInt(javaMulInt(q,_y),r)))<<SC>>
		return new Invariant(suggestedInvariant);
	}

	
}