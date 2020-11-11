/*
 package de.uka.ilkd.key.loopinvgen;
 
import java.lang.reflect.Array;
import java.text.DateFormat.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import com.sun.javafx.fxml.expression.Expression;
import com.sun.xml.internal.bind.v2.schemagen.xmlschema.TopLevelAttribute;
import com.sun.xml.internal.bind.v2.schemagen.xmlschema.TopLevelElement;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.ProgramVariableName;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.strategy.feature.TopLevelFindFeature;

public class ReadProof {

	private final Goal goal;
	private final Services services;
	private final TermBuilder tb;

	public ReadProof(Goal g) {
		goal = g;
		services = goal.proof().getServices();
		tb = services.getTermBuilder();

	}

	public SourceElement getLoopFormula() {
		for (SequentFormula sf : goal.sequent().succedent()) {
			// System.out.println(ProofSaver.printTerm(sf.formula(), services));
			if (sf.formula().op() instanceof UpdateApplication) {
				Term belowUpdate = UpdateApplication.getTarget(sf.formula());
				if (belowUpdate.op() == Modality.DIA) {
					JavaBlock block = belowUpdate.javaBlock();
					ProgramElement pe = block.program();
					if (pe instanceof ProgramPrefix) {
						SourceElement activePE = ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
						if (activePE instanceof While) {
							System.out.println("Loop Formula: " + activePE);
							return activePE;
						}
					}
				}
			}
		}
		return null;
	}

	public Semisequent getAntecedent() {
		Semisequent ant = null;
		if (goal.sequent().antecedent() != null)
			ant = goal.sequent().antecedent();
			System.out.println(" Antecedent: " + goal.sequent().antecedent());

		//for (SequentFormula sf : goal.sequent().antecedent()) {
//			if (sf.formula().op() instanceof DependencePredicate || sf.formula().op() instanceof AccessPredicate) {
//				res.add(sf);
//			}
		//}
// Uncomment after adding the shifting rule		
//		if (res != null)
//			for (int i = 0; i < res.size(); i++) {
//				System.out.println(res.get(i));
//			}
		return ant;
	}



	
	public Set<Term> collectAllSubterms(Sequent s) {
	    TermCollector collector = new TermCollector();
		for (SequentFormula sf : s) {
			sf.formula().execPostOrder(collector);
		}
	    
	    return collector.getTerms();		
	}
	
	
	
	public void getArray() {
//		Set<Term> pvf = null;
//		Semisequent seq = goal.sequent().succedent();
//		for (SequentFormula sf : seq) {
//			if(sf.formula().op() instanceof ProgramVariable || sf.formula().op() instanceof Field)
//				//TODO
//		}
}

	public Statement getLoopBody() {
		Statement body = ((LoopStatement) this.getLoopFormula()).getBody();
		System.out.println("Loop body: " + body);
		return body;
	}

	
	
//	public void consAccessedLocSets(Statement body) {
//		ConstructAccessedLocations caLocs = new ConstructAccessedLocations((ProgramElement) body, this.services);
//		System.out.println("written locs: " + caLocs.wLocs);
//		System.out.println("read locs: " + caLocs.rLocs);
//	}

//	public Term getInvFromSpec() {
//		SourceElement activePE = this.getLoopFormula();
//		LoopSpecification ls = services.getSpecificationRepository().getLoopSpec((While) activePE);
//
//		System.out.println("Existing Loop Inv: " + ls.getInvariant(services));
//		return ls.getInvariant(services);
//	}

//	public void setInvInSpec(Term val) {
//		val = tb.equals(tb.add(tb.zTerm(5), tb.zTerm(1)), tb.zTerm(6));
//		SourceElement activePE = this.getLoopFormula();
//
//		Map<LocationVariable, Term> invariants = new HashMap<>();
//		invariants.put((LocationVariable) tb.getBaseHeap().op(), val);
//
//		LoopSpecification ls = services.getSpecificationRepository().getLoopSpec((While) activePE);
//		LoopSpecification newLS = ls.setInvariant(invariants, new HashMap<>(), null, null, services);
//		services.getSpecificationRepository().addLoopInvariant(newLS);
//		System.out.println("New Loop Inv: " + newLS);
//	}

//	public Term genLI() {
//		Statement body = ((LoopStatement) this.getLoopFormula()).getBody();
//		ProgramElement root = (ProgramElement) services.getProof().root();
//		ConstructAccessedLocations caLocs = new ConstructAccessedLocations(root, services);
//		caLocs.collectReadAndWrittenPVs(root);
//		caLocs.mainFunc();
//		
//		ConstructAllPredicates capR = new ConstructAllPredicates(caLocs.rArr, services);
//		capR.mainFunc();
//		ConstructAllPredicates capW = new ConstructAllPredicates(caLocs.wArr, services);
//		capW.mainFunc();
//		ConstructAllPredicates capRUnionW = new ConstructAllPredicates(caLocs.rUnionWArr, services);
//		capRUnionW.mainFunc();
//		ConstructAllPredicates capRIntersectW = new ConstructAllPredicates(caLocs.rIntersectWArr, services);
//		capRIntersectW.mainFunc();
//		ConstructAllPredicates capRMinusW = new ConstructAllPredicates(caLocs.rMinusWArr, services);
//		capRMinusW.mainFunc();
//		ConstructAllPredicates capWMinusRArr = new ConstructAllPredicates(caLocs.wMinusRArr, services);
//		capWMinusRArr.mainFunc();		
//	
//		ConjuctionConstruction cc = new ConjuctionConstruction(services);
//		//vali in alan faghat and hame ra midahad, dar halike bayad hameye tarkibate mokhtalef ra tolid konad
//		Term t = tb.and(cc.conjuctionOfAll(caPr),cc.conjuctionOfAll(caPw),cc.conjuctionOfAll(caPrUw), cc.conjuctionOfAll(caPrIw), cc.conjuctionOfAll(caPrMw), cc.conjuctionOfAll(caPwMr));
//		return t;
//	}

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

}*/
