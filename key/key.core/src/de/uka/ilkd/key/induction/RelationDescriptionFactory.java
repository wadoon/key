package de.uka.ilkd.key.induction;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

public class RelationDescriptionFactory {
	
	public static List<RelationDescription> generate(Term term, Services services){
		LinkedList<RelationDescription> rds = new LinkedList<RelationDescription>();
		if(term.op().arity() > 0){
			rds.add(new RelationDescription(term, services));
			for(Term sub : term.subs()){
				rds.addAll(generate(sub, services));
			}
		}
		return rds;
	}
}
