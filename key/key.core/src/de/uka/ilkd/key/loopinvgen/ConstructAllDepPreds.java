package de.uka.ilkd.key.loopinvgen;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;

public class ConstructAllDepPreds {

	private final Goal goal;
	private final Services services;
	private final TermBuilder tb;
	private int i, l, h;
	private Term[] a;
	public Set<Term> depPredList = new HashSet<>();
	public ConstructAllDepPreds(Goal g, Term array[], int low, int index, int high) {
		goal = g;
		services = goal.proof().getServices();
		tb = services.getTermBuilder();
		this.a = array;
		this.l = low;
		this.i = index;
		this.h = high;

		// services.getTypeConverter().getLocSetLDT().getArrayRange();

	}

	@SuppressWarnings("null")
	private Term[][] subArrCons(Term[] a, int low, int high) {
		Term[][] sub = null;
		
		for (int i = 0; i < high - low + 1; i++) {
			sub[0][i] = Arrays.copyOfRange(a, low, high)[i];
		}

		for (int i = 0; i < high - low + 2; i++) {
			sub[1][i] = Arrays.copyOfRange(a, low, high + 1)[i];
		}

		for (int i = 0; i < high - low; i++) {
			sub[2][i] = Arrays.copyOfRange(a, low + 1, high)[i];
		}

		for (int i = 0; i < high - low + 1; i++) {
			sub[3][i] = Arrays.copyOfRange(a, low + 1, high + 1)[i];
		}
		return sub;
	}

	@SuppressWarnings("null")
	private Set<Term> predCons(Term[] subArr) {
		Set<Term> depPreds = new HashSet<>();
		
		if (subArr != null) {
			depPreds.add(tb.noR(subArr));
			depPreds.add(tb.noW(subArr));
			depPreds.add(tb.noRaW(subArr));
			depPreds.add(tb.noWaR(subArr));
			depPreds.add(tb.noWaW(subArr));
		}
		return depPreds;
	}

	@SuppressWarnings("null")
	public void cons() {
		
		Term[][] sub0 = subArrCons(this.a, this.l, this.h);
		for (int i = 0; i < sub0.length; i++) {
			depPredList.addAll(predCons(sub0[i]));
		}

		Term[][] sub1 = subArrCons(this.a, this.l, this.i);
		for (int i = 0; i < sub1.length; i++) {
			depPredList.addAll(predCons(sub1[i]));
		}

		Term[][] sub2 = subArrCons(this.a, this.i, this.h);
		for (int i = 0; i < sub2.length; i++) {
			depPredList.addAll(predCons(sub2[i]));
		}

		Term[][] sub3 = subArrCons(this.a, this.l, this.l);
		for (int i = 0; i < sub3.length; i++) {
			depPredList.addAll(predCons(sub3[i]));
		}

		Term[][] sub4 = subArrCons(this.a, this.i, this.i);
		for (int i = 0; i < sub4.length; i++) {
			depPredList.addAll(predCons(sub4[i]));
		}
		
		Term[][] sub5 =	subArrCons(this.a, this.h, this.h);
		for (int i = 0; i <sub5.length; i++) {
			depPredList.addAll(predCons(sub5[i]));
		}
		System.out.println(depPredList);
	}
}