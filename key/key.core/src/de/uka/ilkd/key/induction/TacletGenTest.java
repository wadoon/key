package de.uka.ilkd.key.induction;

import java.util.LinkedList;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;

public class TacletGenTest {

	private Term term;
	private Services services;
	
	public TacletGenTest(Term t, Services s) {
		term = t;
		services = s;
	}
	
	public void tacletGen(){
		//create Taclet
		TacletGenerator generator = TacletGenerator.getInstance();
		Name tacletName = new Name("testtaclet");
		RuleSet ruleset = (RuleSet)services.getNamespaces().ruleSets().elements().head();//TODO: check if this works
		ImmutableList<ProgramVariable> programVars = ImmutableSLList.nil();
		Namespace progVarNamespace = services.getNamespaces().programVariables();
		//TODO: programVars = ??? (progVars)
		Taclet tac = generator.generateRewriteTaclet(
				tacletName, //muss eindeutig sein
				term,
				term, 
				programVars, 
				ruleset, 
				services
				);
		
		//services.getSpecificationRepository() //RuleJustification?
		
				
		//ONLY FOR TESTING
		System.out.println(tac.toString());
		System.out.println(services.getProfile().getJustification(tac).toString());
		
		SVInstantiations insts = SVInstantiations.EMPTY_SVINSTANTIATIONS;
		services.getProof().openGoals().head().addTaclet(tac, insts, true);
		
	}
}
