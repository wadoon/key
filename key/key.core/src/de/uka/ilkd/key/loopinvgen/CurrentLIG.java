package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;

public class CurrentLIG {

	private final Goal goal;
	private final Services services;
	private final TermBuilder tb;
	
	public CurrentLIG (Goal g) {
		goal = g;
		services = goal.proof().getServices();
		tb = services.getTermBuilder();
	}
	
	public void mainAlg() {
		int low = 0;
		getLocSet();
		getIndexes();
//		ConstructAllCompPreds cac = new ConstructAllCompPreds(low, index, high);
//		ConstructAllDepPreds cad = new ConstructAllDepPreds(goal, array, low, index, high);
//		PredicateRefinement pr = new PredicateRefinement(goal, cac.consAllCompPreds(), cad.depPredList);
	}

	private void getIndexes() {
		for (SequentFormula sf : goal.sequent().succedent()) {
			// System.out.println(ProofSaver.printTerm(sf.formula(), services));
			
				if (sf.formula().op() == Modality.DIA) {
					JavaBlock block = sf.formula().javaBlock();
					ProgramElement pe = block.program();
					if (pe instanceof ProgramPrefix) {
						SourceElement activePE = ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
						if (activePE instanceof While) {
							System.out.println("Loop Formula: " + activePE);
							ProgramElement p = ((While) activePE).getGuard().getChildAt(1);
							/* if (p is < or <= )
							 * 		then low := getChildAt(0) & high := getChildAt(2);
							 * if else (p is > or >= )
							 * 		then low := getChildAt(2) & high := getChildAt(0)
							 */
							//return activePE;
						}
					}
				}
			
		}
//		return null;
		
	}

	private void getLocSet() {
		// How to find the targeted location set?
		
	}
	
}
