package prover;
import de.uka.ilkd.key.logic.Term;

public class Invariant implements InvGenResult {

	private Term myFormula;
	
	public Invariant(Term formula) {
		myFormula = formula;
	}
	
	public Term getFormula() {
		return myFormula;
	}
	
}
