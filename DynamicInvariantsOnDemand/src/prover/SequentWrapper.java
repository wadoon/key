package prover;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

public class SequentWrapper {

	private TermBuilder myTermBuilder;
	
	private List<Term> myGamma;
	private Term myUpdate;
	private StatementBlock myProgram;
	private Term myPhi;
	
	public SequentWrapper(Sequent sequent, TermBuilder termBuilder) {
		myTermBuilder = termBuilder;
		myGamma = new ArrayList<>();
		for(SequentFormula currentSequent : sequent.antecedent().asList() ) {
			myGamma.add(currentSequent.formula());
		}
		for(SequentFormula currentSequent : sequent.succedent().asList() ) {
			if(!currentSequent.formula().containsJavaBlockRecursive()) {
				myGamma.add(myTermBuilder.not(currentSequent.formula()));
			} else {
				myUpdate = currentSequent.formula().sub(0);
				myProgram = ((StatementBlock)currentSequent.formula().sub(1).javaBlock().program()).getInnerMostMethodFrame().getBody();
				myPhi = currentSequent.formula().sub(1).sub(0);
			}
		}
	}
	
	public List<Term> getGamma() {
		return myGamma;
	}
	public Term getUpdate() {
		return myUpdate;
	}
	public StatementBlock getProgram() {
		return myProgram;
	}
	public While getLoop() {
		if (myProgram == null)
			return null;
		SourceElement currentSourceElement = myProgram.getFirstElement();
		while( !(currentSourceElement instanceof While) ) {
			currentSourceElement = currentSourceElement.getFirstElement();
		}
		While loop = null;
		if (currentSourceElement instanceof While)
			loop = (While)currentSourceElement;
		
		//return null, if no loop
		return loop;
	}
	public Term getPhi() {
		return myPhi;
	}
	
	@Override
	public String toString() {
		String result = "";
		boolean first = true;
		for(Term currentTerm : myGamma) {
			if(!first) result = result + ",";
			result = result + currentTerm;
			first = false;
		}
		result = result + " ==> ";
		result = result + myUpdate + "[" + myProgram + "]" + myPhi;
		return result;
	}
	
}
