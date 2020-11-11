package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.EventUpdate;
import de.uka.ilkd.key.logic.op.UpdateSV;
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

	public Sequent shiftUpdate() {
		if(inSeq.succedent().get(0).formula().op() instanceof EventUpdate) {
			outSeq = shiftEventUpdate(inSeq);
		}
		else if(inSeq.succedent().get(0).formula().op() instanceof UpdateSV) {
			outSeq = shiftNormalUpdate(inSeq);
		}
		return outSeq;
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
