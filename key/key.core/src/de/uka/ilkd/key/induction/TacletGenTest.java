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
		
		ImmutableList<ProgramVariable> programVars = null;
		Taclet tac = generator.generateRewriteTaclet(
				tacletName, 
				term,
				term, 
				programVars, 
				services.getNamespaces().ruleSets(), 
				services
				);
	}
	
	private TacletGenerator getTacletGenerator(){
		//TODO: get a tacletgenerator.
		return TacletGenerator.getInstance();
	}

}
