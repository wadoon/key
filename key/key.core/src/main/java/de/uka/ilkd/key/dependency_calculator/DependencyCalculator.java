package de.uka.ilkd.key.dependency_calculator;

import java.util.HashSet;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.ClassInvariant;

public class DependencyCalculator {

	public static HashSet<Term> calculateDependenciesForInvariants(Proof proof, KeYJavaType kjt){
		System.out.println("Start calculating dependencies");
		
		Services services = proof.getServices();
		HashSet<Term> dependencies = new HashSet<Term>();
		LogicVariable self = new LogicVariable(new Name("self"), kjt.getSort());
		
		ImmutableSet<ClassInvariant> invariants = proof.getServices().getSpecificationRepository().getClassInvariants(kjt);
		
		for(ClassInvariant inv: invariants){
			dependencies.addAll(calculateDependenciesForInvariant(inv, services, self, kjt));
		}
		
		return dependencies;
	}
	
	private static HashSet<Term> calculateDependenciesForInvariant(ClassInvariant invariant, Services services, LogicVariable self, KeYJavaType kjt){
								
		DepVisitor depVisitor = new DepVisitor(services, kjt);
		invariant.getInv(self, services).execPostOrder(depVisitor);

		return depVisitor.getDependencies();
	}
}
