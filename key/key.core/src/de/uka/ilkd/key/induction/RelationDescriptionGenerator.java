package de.uka.ilkd.key.induction;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;

public class RelationDescriptionGenerator {
	
	private final static List<String> IGNORED_OPERATORS = Arrays.asList("all", "equals");
	
	public static List<RelationDescription> generate(Term term, Services services){
		LinkedList<RelationDescription> rds = new LinkedList<RelationDescription>();
		Operator op = term.op();
		if(op.arity() > 0){
			if(IGNORED_OPERATORS.contains(op.name().toString())){
				rds.add(new RelationDescription(term, services));
			}
			for(Term sub : term.subs()){
				rds.addAll(generate(sub, services));
			}
		}
		return rds;
	}
	
}
