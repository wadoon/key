package de.uka.ilkd.keyabs.rule.metaconstruct;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.keyabs.abs.ABSProgramElement;

public class MethodArgsToSeq extends AbstractTermTransformer {

    public MethodArgsToSeq() {
	super(new Name("#methodArgsToSeq"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, IServices services) {
	SchemaVariable sv = (SchemaVariable) term.sub(0).op();
	
	Iterable<ABSProgramElement> args = (Iterable<ABSProgramElement>) svInst.getInstantiation(sv);
	
	Debug.assertTrue(args instanceof Iterable);
	TermBuilder TB = services.getTermBuilder();
	Term seq = TB.seqEmpty(services); 
	for (ABSProgramElement pe : args) {
	    seq = TB.seqConcat(services, seq, TB.seqSingleton(services, services.getTypeConverter().convertToLogicElement(pe)));
	}
	
	return seq;
    }

}
