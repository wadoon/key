package de.uka.ilkd.key.specgen.generator.dynamic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

public class DynamicSpecGenerator {
	
	private Services myServices;
	
	public DynamicSpecGenerator(Services services) {
		myServices = services;
	}
	
	public Term generate(Sequent sequent) {
		TermBuilder termBuilder  = myServices.getTermBuilder();
		Term loopInvariant = termBuilder.TRUE();
		//DefaultTermParser parser = new DefaultTermParser();
		//Term loopInvariant = parser.parse(new StringReader("true"), Sort.FORMULA, myServices, myServices.getNamespaces(), null);
		return loopInvariant;
	}

}
