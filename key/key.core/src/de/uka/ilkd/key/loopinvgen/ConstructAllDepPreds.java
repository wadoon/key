package de.uka.ilkd.key.loopinvgen;

import java.util.ArrayList;
import java.util.Arrays;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;

public class ConstructAllDepPreds {

	private final Goal goal;
	private final Services services;
	private final TermBuilder tb;
	private int i, l, h;
	private Sort[] a;

	public ConstructAllDepPreds(Goal g, Sort a[], int l, int i, int h) {
		goal = g;
		services = goal.proof().getServices();
		tb = services.getTermBuilder();
		this.a = a;
		this.l = l;
		this.i = i;
		this.h = h;

		// services.getTypeConverter().getLocSetLDT().getArrayRange();

	}

	@SuppressWarnings("null")
	private Sort[][] subArrCons(Sort[] a, int low, int high) {
		Sort[][] sub = null;
		
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
	private ArrayList<DependencePredicate> predCons(Sort[] arg) {
		ArrayList<DependencePredicate> depPredList = null;
		if (arg != null) {
			depPredList.add(new NoRDependencePredicate(arg));
			depPredList.add(new NoWDependencePredicate(arg));
			depPredList.add(new NoRAWDependencePredicate(arg));
			depPredList.add(new NoWARDependencePredicate(arg));
			depPredList.add(new NoWAWDependencePredicate(arg));
		}
		return depPredList;
	}

	@SuppressWarnings("null")
	public ArrayList<DependencePredicate> cons() {
		ArrayList<DependencePredicate> depPredList = null;
		Sort[][] sub0 = subArrCons(this.a, this.l, this.h);
		for (int i = 0; i < sub0.length; i++) {
			depPredList.addAll(predCons(sub0[i]));
		}

		Sort[][] sub1 = subArrCons(this.a, this.l, this.i);
		for (int i = 0; i < sub1.length; i++) {
			depPredList.addAll(predCons(sub1[i]));
		}

		Sort[][] sub2 = subArrCons(this.a, this.i, this.h);
		for (int i = 0; i < sub2.length; i++) {
			depPredList.addAll(predCons(sub2[i]));
		}

		Sort[][] sub3 = subArrCons(this.a, this.l, this.l);
		for (int i = 0; i < sub3.length; i++) {
			depPredList.addAll(predCons(sub3[i]));
		}

		Sort[][] sub4 = subArrCons(this.a, this.i, this.i);
		for (int i = 0; i < sub4.length; i++) {
			depPredList.addAll(predCons(sub4[i]));
		}
		
		Sort[][] sub5 =	subArrCons(this.a, this.h, this.h);
		for (int i = 0; i <sub5.length; i++) {
			depPredList.addAll(predCons(sub5[i]));
		}
		System.out.println(depPredList);
		return depPredList;
	}
}