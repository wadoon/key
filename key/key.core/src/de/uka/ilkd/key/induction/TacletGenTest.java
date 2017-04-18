package de.uka.ilkd.key.induction;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;

public class TacletGenTest {

	private Term term;
	private Services services;
	
	public TacletGenTest(Term t, Services s) {
		term = t;
		services = s;
	}
	
	public void tacletGen(){
		TacletGenerator generator = getTacletGenerator();
		
		Name tacletName = new Name("testtaclet");
		RuleSet ruleset = (RuleSet)services.getNamespaces().ruleSets().elements().head();//TODO: check if this works
		
		//TODO: fix ClassCastException here
		ImmutableList<ProgramVariable> programVars = (ImmutableList<ProgramVariable>) services.getNamespaces().programVariables();
		Taclet tac = generator.generateRewriteTaclet(
				tacletName, 
				term,
				term, 
				programVars, 
				ruleset, 
				services
				);
		
		//ONLY FOR TESTING
		System.out.println(tac.toString());
		
	}
	
	private TacletGenerator getTacletGenerator(){
		//TODO: get a tacletgenerator.
		return TacletGenerator.getInstance();
	}

}
