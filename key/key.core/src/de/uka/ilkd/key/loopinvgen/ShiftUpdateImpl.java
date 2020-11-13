package de.uka.ilkd.key.loopinvgen;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;

public class ShiftUpdateImpl {
	public Sequent outSeq;
	private final Sequent inSeq;
	private final Goal goal;
	private final Services services;
	private final TermBuilder tb;
	private Name rPred, wPred;
	
	public ShiftUpdateImpl(Goal g) {
		goal = g;
		services = g.proof().getServices();
		inSeq = goal.sequent();
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
	            shiftEventUpdate(update,g,pos);
	        } else if (update.op() == UpdateJunctor.SKIP) {
	            // intentionally empty
	        } else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
	            updateList = updateList.prepend(update.sub(1)).prepend(update.sub(0));
	        }	        
	    }	  
	}
	
	//update: a:=t
	private void shiftElementaryUpdate(Term update, Goal g, PosInOccurrence pos) {
        ElementaryUpdate eU = (ElementaryUpdate) update.op();
        Term target = (Term) eU.lhs();

        //////////Defininf u' update: a:=a'//////////
        
        //Defining a fresh constant symbol a'
        final Name freshConsSymb = new Name(tb.newName(eU.lhs().name().toString(), services.getNamespaces()));
    	final Function freshConsFunc = new Function(freshConsSymb, eU.lhs().sort(), true);
    	services.getNamespaces().functions().addSafely(freshConsFunc);
    	final Term freshCons = tb.func(freshConsFunc);
    	//Assigning it to a: a := a'
        Term u_prime = tb.elementary(target, freshCons);
        
        //then it has to be applied to all of the left side
        Term u_prime_target = (Term)goal.sequent().antecedent();
        Term u_prime_application = tb.apply(u_prime, u_prime_target);
        //First remove the antecedent then:
        // Ask Richard how to replace the whole antecident with the new one?
        g.addFormula((SequentFormula)u_prime_application, true, true);
        //////////////////////////////////////////////////
        
        
        //////////Defining upd which is not an update but an assignment: a={u'}{u}a//////////
        
        
        
        //then it has to be added to the left side
        //////////////////////////////
        
    }

    private void shiftEventUpdate(Term update, Goal g, PosInOccurrence pos) {
        Term term4EventUpdate;
        
        if (update.sub(0).toString().equals("read")) 
            term4EventUpdate = tb.rPred(update.sub(1), tb.add(update.sub(2), tb.zTerm(1)));
        else if(update.sub(0).toString().equals("write"))
            term4EventUpdate = tb.wPred(update.sub(1), tb.add(update.sub(2), tb.zTerm(1)));
        else 
            throw new RuntimeException("Unknown event update");
        
        g.addFormula(new SequentFormula(term4EventUpdate), true, true);
	}
	
	
	private Sequent shiftEventUpdate(Sequent inSq) {
		Term accPred = null;
		
		Term eUpd= ((Term)inSq.succedent().getFirst().formula().op());
				
		
		inSq.succedent().remove(0);
		
		
		
		if(eUpd.sub(0).toString().equals("read")) 
			accPred = tb.rPred(eUpd.sub(1), tb.add(eUpd.sub(2), tb.zTerm(1)));
		else if(eUpd.sub(0).toString().equals("write"))
			accPred = tb.wPred(eUpd.sub(1), tb.add(eUpd.sub(2), tb.zTerm(1)));
		
		inSq.addFormula((SequentFormula)accPred, true, false);
		return inSq;
	}
	
	private Sequent shiftNormalUpdate(Sequent inSq) {
		Sequent outSq = null;
	
		
		
		return outSq;
		
	}
}
