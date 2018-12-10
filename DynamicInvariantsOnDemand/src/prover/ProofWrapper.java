package prover;
import de.uka.ilkd.key.proof.Proof;

public class ProofWrapper implements ProofResult {

	private Proof myProof;
	
	public ProofWrapper(Proof proof) {
		myProof = proof;
	}
	
}
