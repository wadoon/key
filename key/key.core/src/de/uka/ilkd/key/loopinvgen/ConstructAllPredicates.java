package de.uka.ilkd.key.loopinvgen;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;

public class ConstructAllPredicates {
	private final Services services;
	private final ImmutableArray<Term> locs;
	private final TermFactory tf;
	
	public Term noRPred = null;
	public Term noWPred = null;
	public Term noRaWPred = null;
	public Term noWaRPred = null;
	public Term noWaWPred = null;
	
	public ConstructAllPredicates(ImmutableArray<Term> locs, Services services) {
		this.services = services;
		this.locs = locs;
		this.tf = services.getTermFactory();
	}
	
	public void constructNoReadPredTerm(ImmutableArray<Term> locs) {
		
		NoReadPredicate noR = new NoReadPredicate();
		this.noRPred = this.tf.createTerm(noR, locs, null, null);
	}
	
	public void constructNoWritePredTerm(ImmutableArray<Term> locs) {

		NoWritePredicate noW = new NoWritePredicate();
		this.noWPred = this.tf.createTerm(noW, locs, null, null);
	}
	
	public void constructNoReadAfterWritePredTerm(ImmutableArray<Term> locs) {

		NoReadAfterWritePredicate noRaW = new NoReadAfterWritePredicate();
		this.noRaWPred = this.tf.createTerm(noRaW, locs, null, null);
	}
	
	public void constructNoWriteAfterReadPredTerm(ImmutableArray<Term> locs) {

		NoReadAfterWritePredicate noWaR = new NoReadAfterWritePredicate();
		this.noWaRPred = this.tf.createTerm(noWaR, locs, null, null);
	}
	
	public void constructNoWriteAfterWritePredTerm(ImmutableArray<Term> locs) {

		NoWriteAfterWritePredicate noWaW = new NoWriteAfterWritePredicate();
		this.noWaWPred = this.tf.createTerm(noWaW, locs, null, null);
	}
	
	public void mainFunc() {
		constructNoReadPredTerm(this.locs);
		constructNoReadAfterWritePredTerm(this.locs);
		constructNoWriteAfterReadPredTerm(this.locs);
		constructNoWritePredTerm(this.locs);
		constructNoWriteAfterWritePredTerm(this.locs);
	}
}
