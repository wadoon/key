package de.uka.ilkd.key.loopinvgen;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;

public class ConstructAllDepPreds {

	private final Services services;
	private final TermBuilder tb;
	private Term i, l, h;
	private Term a;
	private Set<Term> depPredList = new HashSet<>();

	public ConstructAllDepPreds(Services s, Term array, Term low, Term index, Term high) {
		this.services = s;
		this.tb = services.getTermBuilder();
		this.a = array;
		this.l = low;
		this.i = index;
		this.h = high;

//		 services.getTypeConverter().getLocSetLDT().getArrayRange();

	}

	private Set<Term> subArrCons(Term arr, Term l, Term h) {
		Set<Term> sub = new HashSet<>();

		sub.add(tb.arrayRange(arr, l, tb.subtract(h, tb.one())));
		sub.add(tb.arrayRange(arr, l, h));
		sub.add(tb.arrayRange(arr, tb.add(l, tb.one()), h));
		sub.add(tb.arrayRange(arr, tb.add(l, tb.one()), tb.subtract(h, tb.one())));
//		System.out.println("sub arrays: " + sub.toString());

		return sub;
	}

	private Set<Term> predCons(Term subArr) {
		Set<Term> depPreds = new HashSet<>();

		depPreds.add(tb.noR(subArr));
		depPreds.add(tb.noW(subArr));
		depPreds.add(tb.noRaW(subArr));
		depPreds.add(tb.noWaR(subArr));
		depPreds.add(tb.noWaW(subArr));

//		System.out.println("dependence predicates: " + depPreds.toString());
		return depPreds;
	}

	Set<Term> cons() {

		Set<Term> sub0 = subArrCons(a, l, h);
		for (Term t : sub0) {
			depPredList.addAll(predCons(t));
		}

		Set<Term> sub1 = subArrCons(a, l, i);
		for (Term t : sub1) {
			depPredList.addAll(predCons(t));
		}

		Set<Term> sub2 = subArrCons(a, i, h);
		for (Term t : sub2) {
			depPredList.addAll(predCons(t));
		}

		depPredList.addAll(predCons(tb.singleton(a, tb.arr(l))));
		depPredList.addAll(predCons(tb.singleton(a, tb.arr(i))));
		depPredList.addAll(predCons(tb.singleton(a, tb.arr(h))));
		
		//TODO: Not sure if this part is needed:
//		depPredList.addAll(predCons(tb.singleton(a, tb.arr(tb.add(l, tb.one())))));
//		depPredList.addAll(predCons(tb.singleton(a, tb.arr(tb.subtract(i, tb.one())))));
//		depPredList.addAll(predCons(tb.singleton(a, tb.arr(tb.add(i, tb.one())))));
//		depPredList.addAll(predCons(tb.singleton(a, tb.arr(tb.subtract(i, tb.one())))));
		
		return depPredList;
	}
}