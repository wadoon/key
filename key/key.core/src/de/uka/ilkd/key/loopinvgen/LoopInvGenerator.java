package de.uka.ilkd.key.loopinvgen;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.LoopSpecification;

public class LoopInvGenerator {
	
	private final Goal goal;
	private final Services services;
	private final TermBuilder tb;

	public LoopInvGenerator(Goal g) {
		goal = g;
		services = goal.proof().getServices();
		tb = services.getTermBuilder();
		
	}
	
	public Term retInvFromSpec() {
		
		for(SequentFormula sf : goal.sequent().succedent()) {
			System.out.println(ProofSaver.printTerm(sf.formula(), services));
			if(sf.formula().op() instanceof UpdateApplication) {
				Term belowUpdate = UpdateApplication.getTarget(sf.formula());
				if(belowUpdate.op() == Modality.DIA) {
					JavaBlock block = belowUpdate.javaBlock();
					ProgramElement pe = block.program();
					if(pe instanceof ProgramPrefix) {
						SourceElement activePE = ((ProgramPrefix)pe).getLastPrefixElement().getFirstElement();
						System.out.println("Check " + activePE);
						if(activePE instanceof While) {
							System.out.println("Found " + pe);
							LoopSpecification ls = services.getSpecificationRepository().getLoopSpec((While)activePE);
							System.out.println("Existing Loop Inv: " + ls.getInvariant(services));
							return ls.getInvariant(services);
						}
					}
				}
			}
		}
		
		return null;
	}
	
	public void setInvInSpec(Term val) {
		val = tb.equals(tb.add(tb.zTerm(5), tb.zTerm(1)),tb.zTerm(6));
		for(SequentFormula sf : goal.sequent().succedent()) {
			System.out.println(ProofSaver.printTerm(sf.formula(), services));
			if(sf.formula().op() instanceof UpdateApplication) {
				Term belowUpdate = UpdateApplication.getTarget(sf.formula());
				if(belowUpdate.op() == Modality.DIA) {
					JavaBlock block = belowUpdate.javaBlock();
					ProgramElement pe = block.program();
					if(pe instanceof ProgramPrefix) {
						SourceElement activePE = ((ProgramPrefix)pe).getLastPrefixElement().getFirstElement();
						System.out.println("Check " + activePE);
						if(activePE instanceof While) {
							System.out.println("Found " + pe);
							Map<LocationVariable,Term> invariants = new HashMap<>();					
							invariants.put((LocationVariable) tb.getBaseHeap().op(), val);
							LoopSpecification ls = services.getSpecificationRepository().getLoopSpec((While)activePE);
							LoopSpecification newLS = ls.setInvariant(invariants, new HashMap<>(), null, null, services);
							services.getSpecificationRepository().addLoopInvariant(newLS);
							System.out.println("New Loop Inv: " + newLS);
						}
					}
				}
			}
		}
	}
	
//	public Term generate() {
//		Services services = goal.proof().getServices();
//		TermBuilder tb = services.getTermBuilder();
//
//		Term loopFormula = null;
//		for (SequentFormula sf : goal.sequent().succedent()) {
//			System.out.println(ProofSaver.printTerm(sf.formula(), services));
//			if (sf.formula().op() instanceof UpdateApplication) {
//				Term belowUpdate = UpdateApplication.getTarget(sf.formula());
//				if (belowUpdate.op() == Modality.DIA) {
//					JavaBlock block = belowUpdate.javaBlock();
//					ProgramElement pe = block.program();
//					if (pe instanceof ProgramPrefix) {
//						SourceElement activePE = ((ProgramPrefix)pe).getLastPrefixElement().getFirstElement();
//						System.out.println("Check " + activePE);
//						if (activePE instanceof While) {					
//							System.out.println("Found " + pe);
//							LoopSpecification ls = 
//									services.getSpecificationRepository().getLoopSpec((While)activePE);
//							System.out.println(ls.getInvariant(services));
//							Map<LocationVariable,Term> invariants = new HashMap<>();
//							
//							
//							
//							invariants.put((LocationVariable) tb.getBaseHeap().op(), 
//									tb.equals(tb.add(tb.zTerm(5), tb.zTerm(1)),tb.zTerm(6)));
//							
//							LoopSpecification newLS = ls.setInvariant(invariants, new HashMap<>(), null, null, services);
//							services.getSpecificationRepository().addLoopInvariant(newLS);
//						}
//					}
//					
//				}
//			}
//		}
//		
//		
//		Term six = tb.equals(tb.add(tb.zTerm(5), tb.zTerm(1)),tb.zTerm(6));
//		System.out.println(six);
//				
//		
//		return null;
//	}

}
