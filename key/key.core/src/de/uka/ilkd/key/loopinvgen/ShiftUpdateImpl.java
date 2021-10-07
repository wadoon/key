package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.EventUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;

public class ShiftUpdateImpl {
	private final Goal goal;
	private final Services services;
	private final TermBuilder tb;

	
	public ShiftUpdateImpl(Goal g) {
		goal = g;
		services = g.proof().getServices();
		tb = services.getTermBuilder();
	}

	public void shiftUpdate(Goal g, PosInOccurrence pos) {

		final Term loopFormula = pos.sequentFormula().formula();
		g.removeFormula(pos);

		final Term renameUpdate = generateRenameUpdate(loopFormula);
		
		// rename all existing formulas in sequent except program formula
		renameFormulasOnSemisequent(renameUpdate, g.sequent().antecedent(), true);
		renameFormulasOnSemisequent(renameUpdate, g.sequent().succedent(), false);

		doShift(renameUpdate, g, pos, loopFormula);

		// add program formula again
		g.addFormula(new SequentFormula(UpdateApplication.getTarget(loopFormula)), pos.isInAntec(), true);
	}

	/**
	 * assumes that the current sequent of the goal contains already all formulas prefixed with the renaming update
	 * the method then generates for each elementary update <code>lhs:=rhs</code> the equation <code>lhs == {renamingUpdate}{lhs:=rhs}lhs</code>
	 * and for each event update <code>\event(kind,ls,ts)</code> the formula <code>{renamingUpdate}'kindPred'(ls,t)</code> where <code>kindPred</code> is
	 * the corresponding dependence predicate for the kind (read or write) of the event update
	 * @param renameUpdate the {@link Term} representing the renaming update
	 * @param g the current {@link Goal}
	 * @param pos the {@link PosInOccurrence} of the loopFormula
	 * @param loopFormula the {@link Term} representing the formula containing the loop 
	 */
	private void doShift(final Term renameUpdate, Goal g, PosInOccurrence pos, final Term loopFormula) {
		ImmutableList<Term> updateList = ImmutableSLList.<Term>nil().prepend(UpdateApplication.getUpdate(loopFormula));
		while (!updateList.isEmpty()) {
			final Term update = updateList.head();
			updateList = updateList.tail();
			if (update.op() instanceof ElementaryUpdate) {
				shiftElementaryUpdate(update, renameUpdate);
			} else if (update.op() instanceof EventUpdate) {
				shiftEventUpdate(update, renameUpdate);
			} else if (update.op() == UpdateJunctor.SKIP) {
				// intentionally empty
			} else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
				updateList = updateList.prepend(update.sub(1)).prepend(update.sub(0));
			}
		}
	}

	/**
	 * constructs the renaming update for the loop formula. It assumes the the loop formula has 
	 * the shape <code>{l1:=r2 || ... || ln:=rn || eventupdates} and constructs an update that
	 * renames each left-hand side of the elementary update <code>li:=ri</code> 
	 * @param loopFormula the {@link Term} with formula containing the loop
	 * @return a parallel update <code>{l1:=l1'|| ... || ln:=ln'}</code> that renames each left hand side of the original update
	 */
	private Term generateRenameUpdate(Term loopFormula) {
		ImmutableList<Term> updateList = ImmutableSLList.<Term>nil().prepend(UpdateApplication.getUpdate(loopFormula));
		
		// collect updated locations
		HashSet<UpdateableOperator> updatedLocations = new HashSet<>();
		while (!updateList.isEmpty()) {
			final Term update = updateList.head();
			updateList = updateList.tail();
			if (update.op() instanceof ElementaryUpdate) {
				updatedLocations.add(((ElementaryUpdate)update.op()).lhs());
			} else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
				updateList = updateList.prepend(update.sub(1)).prepend(update.sub(0));
			}	
		}
		
		// create renaming update
		ImmutableList<Term> renameUpdates = ImmutableSLList.<Term>nil();
		for(UpdateableOperator lhs : updatedLocations) {
			// Defining a fresh constant symbol a'
			final Name freshConsSymb = new Name(tb.newName("f_"+lhs.name().toString(), services.getNamespaces()));
			final Function freshConsFunc = new Function(freshConsSymb, lhs.sort(), true);
			services.getNamespaces().functions().addSafely(freshConsFunc);
			final Term freshCons = tb.func(freshConsFunc);
//			System.out.println("a' is: " + freshCons.toString());
			// Assigning it to a: a := a' and adding to list of rename updates
			renameUpdates = renameUpdates.prepend(tb.elementary(lhs, freshCons));
		}
		final Term renameUpdate = tb.parallel(renameUpdates);
		return renameUpdate;
	}

	/**
	 * applies the renaming update on each formula of the given semisequent
	 * @param renameUpdate the {@link Term} representing the renaming update
	 * @param semi the {@link Semisequent} 
	 * @param antec a boolean being true if the semisequent is the antecedent of {@link #goal}
	 */
	private void renameFormulasOnSemisequent(final Term renameUpdate, Semisequent semi, boolean antec) {
		for (SequentFormula sf : semi) { 
			final PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), antec);
			goal.changeFormula(new SequentFormula(tb.apply(renameUpdate, sf.formula())), pio);
		}
	}
	
	/**
	 * constructs for an elementary update <code>lhs:=rhs</code> the equation <code>lhs == {renamingUpdate}{lhs:=rhs}lhs</code>
	 * @param update a {@link Term} denoting the elementary update (assumes {@link ElementaryUpdate} as top level operator) 
	 * @param renamingUpdate the {@link Term} representing the renaming update
	 */
	private void shiftElementaryUpdate(Term update, Term renamingUpdate) {
		ElementaryUpdate eU = (ElementaryUpdate) update.op();// update: a:=t
		Term target = tb.var(eU.lhs()); // a
		// ********** Defining upd which is not an update but an assignment:
		// a={u'}{u}a
		Term u_on_a = tb.apply(update, target);
		Term u_prime_on_u_on_a = tb.apply(renamingUpdate, u_on_a);
		Term a_ass_up_u_a = tb.equals(target, u_prime_on_u_on_a);
		// then it has to be added to the left side
		goal.addFormula(new SequentFormula(a_ass_up_u_a), true, false);
	}

	/**
	 * adds for one event update <code>\event(kind,ls,ts)</code> the formula <code>{renamingUpdate}'kindPred'(ls,t)</code> where <code>kindPred</code> is
	 * the corresponding dependence predicate for the kind (read or write) of the event update
	 * @param update the {@link Term} with an event update at top level
	 * @param renamingUpdate the {@link Term} representing the renaming update
	 */
	

//	private void shiftEventUpdate(Term update, Term renamingUpdate) {
//		Term term4EventUpdate;
//		if (update.sub(0).op().equals(services.getTypeConverter().getDependenciesLDT().getReadMarker()))
//			term4EventUpdate = tb.rPred(update.sub(1), update.sub(2)); 
//		else if (update.sub(0).op().equals(services.getTypeConverter().getDependenciesLDT().getWriteMarker()))
//			term4EventUpdate = tb.wPred(update.sub(1), update.sub(2));
//		else if (update.sub(0).op().equals(services.getTypeConverter().getDependenciesLDT().getNothingMarker()))
//			term4EventUpdate = tb.skip();
//		else
//			throw new RuntimeException("Unknown event update");
//
//		goal.addFormula(new SequentFormula(tb.apply(renamingUpdate, term4EventUpdate)), true, true);
//	}
	
	private void shiftEventUpdate(Term update, Term renamingUpdate) {
		Term t1 = update.sub(0);
		Term t2 = tb.func(services.getTypeConverter().getDependenciesLDT().getReadMarker());
		Term cond1 = tb.equals(t1, t2);
		Term t3 = tb.func(services.getTypeConverter().getDependenciesLDT().getWriteMarker());
		Term cond2 = tb.equals(t1, t3);
		
		final Term term4EventUpdate = tb.ife(cond1, tb.rPred(update.sub(1), update.sub(2)), tb.ife(cond2, tb.wPred(update.sub(1), update.sub(2)), tb.tt()));
		goal.addFormula(new SequentFormula(tb.apply(renamingUpdate, term4EventUpdate)), true, true);
	}

}
