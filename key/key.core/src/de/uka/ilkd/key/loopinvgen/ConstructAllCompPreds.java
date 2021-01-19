package de.uka.ilkd.key.loopinvgen;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

public class ConstructAllCompPreds {

	private final Services services;
	private final TermBuilder tb;
	private Term low, idx, high;
	private Set<Term> compPredList = new HashSet<>();
	public ConstructAllCompPreds(Services service, Term low, Term index, Term high) {
		this.services = service;
		this.tb = services.getTermBuilder();
		
		this.low = low;
		this.idx = index;
		this.high = high;
	}

	private Set<Term> consCompPreds(Term lh, Term rh) {
		Set<Term> list = new HashSet<>();

		list.add(tb.lt(lh, rh));
		list.add(tb.leq(lh, rh));
		list.add(tb.gt(lh, rh));
		list.add(tb.geq(lh, rh));
		list.add(tb.equals(lh, rh));

		return list;
	}

	Set<Term> cons() {
		
		compPredList.addAll(consCompPreds(this.low, this.idx));
		compPredList.addAll(consCompPreds(this.low, this.high));
		compPredList.addAll(consCompPreds(this.idx, this.high));
		
//		System.out.println("Comparison predicates: " + compPredList.toString());
//		System.out.println("Comparison predicates number: " + compPredList.size());
		return compPredList;

	}
}
