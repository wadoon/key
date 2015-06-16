package de.uka.ilkd.keyabs.rule.metaconstruct;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.logic.ldt.HistoryLDT;

public class Retrieve extends AbstractTermTransformer {
	
	
	public Retrieve() {
		super(new Name("#retrieve"), 1);
	}

	@Override
	public Term transform(Term term, SVInstantiations svInst, IServices services) {
		final Term retrieveTerm = term.sub(0);
		final Term eventSequence = retrieveTerm.sub(0);
		final Term eventType     = retrieveTerm.sub(1);
		final Term callee = retrieveTerm.sub(2);
		final Term future = retrieveTerm.sub(3);
		final Term methodLabel = retrieveTerm.sub(4);
		final Term methodArguments = retrieveTerm.sub(5);
		
		SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();

		Term result = retrieve((ABSServices) services, eventSequence, eventType, callee,
				future, methodLabel, methodArguments, seqLDT);

		if (result == null) {
			return retrieveTerm;
		}
		return result; 
	}

	private Term retrieve(ABSServices services, final Term eventSequence,
			final Term eventType, final Term callee, final Term future,
			final Term methodLabel, final Term methodArguments, SeqLDT ldt) {
		TermBuilder<ABSServices> tb = services.getTermBuilder();
		final Term zero = tb.zero(services);
		final Term minusOne = tb.zTerm(services, "-1");
		
		Term result = null;
		
		if (eventSequence.op() == ldt.getSeqEmpty()) {
			result = minusOne;
		} else if (eventSequence.op() == ldt.getSeqSingleton()) {
			Boolean checkResult = check(eventSequence.sub(0), eventType, callee, future, 
					methodLabel, methodArguments, services);
			if (checkResult == null) {
				return null;
			} else if (checkResult.booleanValue()) {
				result = zero;
			} else {
				result = minusOne;
			}
		} else if (eventSequence.op() == ldt.getSeqConcat()) {
			result = retrieve(services, eventSequence.sub(1), eventType, callee,
					future, methodLabel, methodArguments, ldt);
			if (result == null) {
				return result;
			} else if (result.equals(minusOne)) {
				result = retrieve(services, eventSequence.sub(0), eventType, callee,
						future, methodLabel, methodArguments, ldt);
			} else {
				result = tb.add(services, 
							tb.seqLen(services, 
								eventSequence.sub(0)), result); 
			}
		} 
		return result;
	}

	private Boolean check(Term eventLabel, Term eventType, Term callee,
			Term future, Term methodLabel, Term methodArguments, IServices services) {		
		HistoryLDT hLDT = ((ABSServices)services).getTypeConverter().getHistoryLDT();
		Operator eventLabelOp = eventLabel.op();
		
		if (hLDT.getEventTypeOf(eventLabelOp) == eventType.op()) {
			if (callee.equalsModRenaming(eventLabel.sub(1))) {
				if (future.equalsModRenaming(eventLabel.sub(2))) {
					if (methodLabel.equalsModRenaming(eventLabel.sub(3))) {
						if (methodArguments.equalsModRenaming(eventLabel.sub(4))) {
							return true;
						}						
					} else {
						if (methodLabel.op() instanceof Function &&
								eventLabel.sub(3).op() instanceof Function) {
							final Function methodInRetrieve = 
									(Function) methodLabel.op();
							final Function methodInEvent = 
									(Function) eventLabel.sub(3).op();
							if (methodInRetrieve.isUnique() && methodInEvent.isUnique()) {
								if (methodInRetrieve != methodInEvent) {
									return false;
								}
							}
						}
					}
				}
			}
		} else {
			return false;
		}
		return null;
	}

}
