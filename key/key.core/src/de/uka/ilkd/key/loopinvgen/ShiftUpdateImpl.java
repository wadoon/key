package de.uka.ilkd.key.loopinvgen;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;

public class ShiftUpdateImpl {
	public Sequent outSeq;
	private final Goal goal;
	private final Services services;
	private final TermBuilder tb;
	private Name rPred, wPred;

	public ShiftUpdateImpl(Goal g) {
		goal = g;
		services = g.proof().getServices();
		tb = services.getTermBuilder();
	}

	public void shiftUpdate(Goal g, PosInOccurrence pos) {

		Term loopFormula = pos.sequentFormula().formula();

		g.removeFormula(pos);
		g.addFormula(new SequentFormula(UpdateApplication.getTarget(loopFormula)), pos.isInAntec(), true);

		ImmutableList<Term> updateList = ImmutableSLList.nil();
		updateList = updateList.prepend(UpdateApplication.getUpdate(loopFormula));

		while (!updateList.isEmpty()) {
			final Term update = updateList.head();
			updateList = updateList.tail();

			if (update.op() instanceof ElementaryUpdate) {
				shiftElementaryUpdate(update, g, pos);
			} else if (update.op() instanceof EventUpdate) {
				shiftEventUpdate(update, g, pos);
			} else if (update.op() == UpdateJunctor.SKIP) {
				// intentionally empty
			} else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
				updateList = updateList.prepend(update.sub(1)).prepend(update.sub(0));
			}
		}
	}

	// update: a:=t
	private void shiftElementaryUpdate(Term update, Goal g, PosInOccurrence pos) {
		ElementaryUpdate eU = (ElementaryUpdate) update.op();// update: a:=t
		System.out.println("eU is: " + eU.toString());
		Term target = tb.var(eU.lhs());// a
		System.out.println("target is: " + target.toString());
		// ********** Defininf u' update: a:=a' :

		// Defining a fresh constant symbol a'
		final Name freshConsSymb = new Name(tb.newName(eU.lhs().name().toString(), services.getNamespaces()));
		final Function freshConsFunc = new Function(freshConsSymb, eU.lhs().sort(), true);
		services.getNamespaces().functions().addSafely(freshConsFunc);
		final Term freshCons = tb.func(freshConsFunc);
		System.out.println("a' is: " + freshCons.toString());
		// Assigning it to a: a := a'
		Term u_prime = tb.elementary(target, freshCons);
		System.out.println("a :=a' is: " + u_prime.toString());
		// then u' has to be applied to all of the left side
		for (SequentFormula sf : goal.sequent().antecedent()) {
			Term u_prime_target = sf.formula();
			PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), true);
			Term u_prime_application = tb.apply(u_prime, u_prime_target);
			goal.sequent().changeFormula(new SequentFormula(u_prime_application), pio);
		}
		System.out.println("u' on the left side is: " + goal.sequent().antecedent().toString());

		// ********** Defining upd which is not an update but an assignment:

		// a={u'}{u}a
		Term u_on_a = tb.apply(update, target);
		Term u_prime_on_u_on_a = tb.apply(u_prime, u_on_a);
		Term a_ass_up_u_a = tb.equals(target, u_prime_on_u_on_a);
		System.out.println("upd is: " + a_ass_up_u_a.toString());
		
		// then it has to be added to the left side
		goal.sequent().addFormula(new SequentFormula(a_ass_up_u_a), true, false);//WHY IT DOESN'T ADD?????
		System.out.println("antc is: " + goal.sequent().antecedent().toString());
	}

	private void shiftEventUpdate(Term update, Goal g, PosInOccurrence pos) {
		Term term4EventUpdate;

		if (update.sub(0).toString().equals("read"))
			term4EventUpdate = tb.rPred(update.sub(1), tb.add(update.sub(2), tb.zTerm(1)));
		else if (update.sub(0).toString().equals("write"))
			term4EventUpdate = tb.wPred(update.sub(1), tb.add(update.sub(2), tb.zTerm(1)));
		else
			throw new RuntimeException("Unknown event update");

		g.addFormula(new SequentFormula(term4EventUpdate), true, true);
	}

	private Sequent shiftEventUpdate(Sequent inSq) {
		Term accPred = null;

		Term eUpd = ((Term) inSq.succedent().getFirst().formula().op());

		inSq.succedent().remove(0);

		if (eUpd.sub(0).toString().equals("read"))
			accPred = tb.rPred(eUpd.sub(1), tb.add(eUpd.sub(2), tb.zTerm(1)));
		else if (eUpd.sub(0).toString().equals("write"))
			accPred = tb.wPred(eUpd.sub(1), tb.add(eUpd.sub(2), tb.zTerm(1)));

		inSq.addFormula((SequentFormula) accPred, true, false);
		return inSq;
	}

	private Sequent shiftNormalUpdate(Sequent inSq) {
		Sequent outSq = null;

		return outSq;

	}
}
