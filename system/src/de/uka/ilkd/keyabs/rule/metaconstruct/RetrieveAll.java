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


public class RetrieveAll extends AbstractTermTransformer  {

	public RetrieveAll() {
		super(new Name("#retrieveAll"), 1);
	}
	
	
	@Override
	public Term transform(Term term, SVInstantiations svInst, IServices services) {
		final Term retrieveTerm = term.sub(0);
		final Term eventSequence = retrieveTerm.sub(0);
		final Term eventType     = retrieveTerm.sub(1);
		final Term another = retrieveTerm.sub(2);
		final Term future = retrieveTerm.sub(3);
		final Term methodLabel = retrieveTerm.sub(4);
		final Term methodArguments = retrieveTerm.sub(5);
		
		SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();

		Term result = retrieveAll((ABSServices) services, eventSequence, eventType, another,
				future, methodLabel, methodArguments, seqLDT);

		if (result == null) {
			return retrieveTerm;
		}
		return result; 
	}
	
	
	private Term retrieveAll(ABSServices services, final Term eventSequence,
			final Term eventType, final Term another, final Term future,
			final Term methodLabel, final Term methodArguments, SeqLDT ldt) {
		TermBuilder<ABSServices> tb = services.getTermBuilder();
		final Term zero = tb.zero(services);
		final Term emptySequence = tb.seqEmpty(services);
		
		Term result = null;
		
		if (eventSequence.op() == ldt.getSeqEmpty()) { // base case: the history is empty
			result = emptySequence; // retrieveAll returns an empty sequence
		} else if (eventSequence.op() == ldt.getSeqSingleton()) { // history contains only one element
			Boolean checkResult = check(eventSequence.sub(0), eventType, another, future, 
					methodLabel, methodArguments, services);
			if (checkResult == null) {
				return null;
			} else if (checkResult.booleanValue()) { // the only element contained in the sequence satisfies the matching criteria
				result = tb.seqConcat(services, emptySequence, zero); // retrieveAll function returns a sequence which contains an element 0, because the only element contained in the sequence is at index 0
			} else { // the only element contained in the sequence does not satisfy the matching criteria
				result = emptySequence;  // so the retrieveAll function returns an empty sequence
			}
		} else if (eventSequence.op() == ldt.getSeqConcat()) { // history contains more than one elements
			result = retrieveAll(services, eventSequence.sub(1), eventType, another,
					future, methodLabel, methodArguments, ldt);
			if (result == null) {
				return result;
			} else if (result.equals(emptySequence)) { // the last element in the history does not satisfies the matching criteria
				result = retrieveAll(services, eventSequence.sub(0), eventType, another, 
						future, methodLabel, methodArguments, ldt); // invoke retrieveAll function on the prefix history
			} else { // the last element in the history satisfies the matching criteria
				result = tb.seqConcat(services, retrieveAll(services, eventSequence.sub(0), eventType, another, future, methodLabel, methodArguments, ldt), 
							tb.add(services, 
									tb.seqLen(services, 
											eventSequence.sub(0)), result));  
			}
		} 
		return result;
	}
	
	
	private Boolean check(Term eventLabel, Term eventType, Term another,
			Term future, Term methodLabel, Term methodArguments, IServices services) {			
		HistoryLDT hLDT = ((ABSServices)services).getTypeConverter().getHistoryLDT();
		Operator eventLabelOp = eventLabel.op();
		
		if (hLDT.getEventTypeOf(eventLabelOp) == eventType.op()) { 
			if (another.equalsModRenaming(eventLabel.sub(1))) { // TODO: since not all the event contains the OID of an object which the current object is communicating with, we need to distinguish the cases for different kinds of events
				if (future.equalsModRenaming(eventLabel.sub(2))) {
					if (methodLabel.equalsModRenaming(eventLabel.sub(3))) { // TODO: since not all the event contains a method name, we need to distinguish the cases for different kinds of events
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
			} // if else () {...} 
		} else {
			return false;
		}
		return null;
	}

}
