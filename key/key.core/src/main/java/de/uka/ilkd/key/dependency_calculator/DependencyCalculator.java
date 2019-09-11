package de.uka.ilkd.key.dependency_calculator;

import java.util.HashSet;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.ClassInvariant;

public class DependencyCalculator {

	public static HashSet<Term> calculateDependenciesForIntermediateInvariants(Proof proof, KeYJavaType kjt){
		System.out.println("Start calculating dependencies");
		
		Services services = proof.getServices();
		HashSet<Term> dependencies = new HashSet<Term>();
		
		ImmutableSet<ClassInvariant> intermediateInvs = proof.getServices().getSpecificationRepository().getClassInvariants(kjt);
		ProgramVariable self = null;
		
		for(ClassInvariant intermediateInv: intermediateInvs){
			
			// Retrieve the concrete invariant matching the intermediate invariant
			ClassInvariant concreteInv = services.getSpecificationRepository().intermediateToConcreteInvariants.get(intermediateInv);
			
			// Mapping was found from intermediate to concrete invariant was found
			if(concreteInv != null) {
				// Only set it once, so the self variable is equal for all computations
				if(self == null) {
					self = concreteInv.getOrigVars().self;
				}
				dependencies.addAll(calculateDependenciesForConcreteInvariant(concreteInv, services, self, kjt));
			}
		}
		return dependencies;
	}
	
	public static HashSet<Term> calculateDependenciesForConcreteInvariant(ClassInvariant invariant, Services services, ProgramVariable self, KeYJavaType kjt){
								
		DepVisitor depVisitor = new DepVisitor(services, kjt);
		invariant.getInv(self, services).execPostOrder(depVisitor);

		return depVisitor.getDependencies();
	}
}
