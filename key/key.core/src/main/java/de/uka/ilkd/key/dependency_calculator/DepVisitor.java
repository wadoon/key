package de.uka.ilkd.key.dependency_calculator;

import java.util.HashSet;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;

public class DepVisitor extends DefaultVisitor {

	private final Services services;
	private final TermBuilder tb;
	private final LocSetLDT locSetLDT;
	private final HeapLDT heapLDT;
	private final KeYJavaType kjt;
	
	
	private HashSet<Term> dependencies;
	
	public DepVisitor(Services services, KeYJavaType kjt) {
		super();
		
		this.services = services;
		this.tb = new TermBuilder(services.getTermFactory(), services);
		this.locSetLDT = this.services.getTypeConverter().getLocSetLDT();
		this.heapLDT = this.services.getTypeConverter().getHeapLDT();
		this.dependencies = new HashSet<Term>();
		this.kjt = kjt;
	}
	
	@Override
	public void visit(Term visited) {
		
		Operator op = visited.op();
		
		// Case : select term
		if(heapLDT.isSelectOp(op)) {
			calculateDepForSelect(visited);
		}
		// Case : quantifier term
		else if(op instanceof Quantifier) {
		
			// Get quantifiedVariables and convert them to terms in order to compare them later 
			HashSet<Term> quantifiedVariablesTerm = visited
					.boundVars()
					.stream()
					.map(x -> tb.var(x))
					.collect(Collectors.toCollection(HashSet::new));
			
			calculateDepForQuantifier(visited, quantifiedVariablesTerm);
		}
		
		// Case: query method
		else if(visited.op() instanceof ProgramMethod) {
			calculateDepForProgramMethod(visited);
		}
	}

	private void calculateDepForProgramMethod(Term term) {
		
		ImmutableSet<Contract> contracts = services.getSpecificationRepository().getContracts(this.kjt, (IObserverFunction)term.op());
		
		for (Contract contract : contracts) {
			dependencies.add(contract.getAccessible(heapLDT.getHeap()));
		}
	}
	
	private void calculateDepForSelect(Term selTerm) {
		
		Term objectOfSel = selTerm.sub(1);
		Term fieldOfSel = selTerm.sub(2);
		
		// Order of conditions is important:
		// First check whether field is array access, if not
		// then check whether field access is not implicit (e.g not <created>)
		if(fieldOfSel.op() == heapLDT.getArr() || !heapLDT.getAttributeForField(fieldOfSel, services).isImplicit()) {
			dependencies.add(tb.singleton(objectOfSel, fieldOfSel));
		}
	}
	
	private void calculateDepForQuantifier(Term quantifierTerm, HashSet<Term> quantifiedVariablesTerm) {
	
		// Create helper set because the dependencies set cannot be modified during the foreach loop
		HashSet<Term> helper = new HashSet<Term>();
		for (Term term : dependencies) {
						
			if(term.op() == locSetLDT.getSingleton()) {
						
				Term potentiallyQuantifiedVarbiable = term.sub(0);
				
				for (Term quantifiedVariable : quantifiedVariablesTerm) {
								
					// Quantified variable is used in subformula of quantifier
					if(potentiallyQuantifiedVarbiable.equalsModIrrelevantTermLabels(quantifiedVariable)) {
						helper.add(tb.allObjects(term.sub(1)));
					}
								
					// Array access in subformula of quantifier
					else if(term.sub(1).op() == heapLDT.getArr()) {
						Term accessIndex = term.sub(1).sub(0);									
						if(quantifiedVariable.equalsModIrrelevantTermLabels(accessIndex)) {
							helper.add(tb.allFields(term.sub(0)));
						}
					}
				}
			}
						
			else if(term.op() == locSetLDT.getAllFields()) {
							
				Term potentiallyQuantifiedVariable = term.sub(0);
				for (Term quantifiedVariable : quantifiedVariablesTerm) {
								
					if(potentiallyQuantifiedVariable.equalsModIrrelevantTermLabels(quantifiedVariable)) {
						helper.add(tb.allLocs());
					}
				}
							
			}
			
			else if(term.op() == locSetLDT.getAllObjects()) {
				
				// Check wheter it is an allObjects(arr(i)), then we know that we quantified over
				// an array type in the subformula.
				if(term.sub(0).op() == heapLDT.getArr()) {
					
					for (Term quantifiedVariable : quantifiedVariablesTerm) {
						
						Term arrayIndex = term.sub(0).sub(0);
						
						if(arrayIndex.equalsModIrrelevantTermLabels(quantifiedVariable)) {
							helper.add(tb.allLocs());
						}
					}
				}
			}
		}
		dependencies.addAll(helper);		
	}
	
	public HashSet<Term> getDependencies(){
		return this.dependencies;
	}
}
