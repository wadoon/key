package de.uka.ilkd.keyabs.rule.metaconstruct;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.keyabs.abs.ABSServices;

public class LocalVariableAnonymizer extends AbstractTermTransformer {
	
	public LocalVariableAnonymizer() {
		super(new Name("#localVariableAnonymizer"), 1, Sort.FORMULA);
	}
	
	@Override
	public Term transform(Term term, SVInstantiations svInst, IServices serv) {
		ABSServices services = (ABSServices) serv;
		Term formulaToAnonymize = term.sub(0);
		ProgramElement body = (ProgramElement) svInst.lookupValue(new Name("body"));
		
		ImmutableSet<ProgramVariable> assignedLocalVars = MiscTools.getLocalOuts(body, services);

		TermBuilder<ABSServices> tb = services.getTermBuilder();
		Term anonUpdate = tb.skip();
		for (ProgramVariable pv : assignedLocalVars) {
			final Name name = new Name(tb.newName(services, pv.name() + "Anon"));
			final Function skolem = new Function(name, pv.sort());
			anonUpdate = tb.parallel(anonUpdate, tb.elementary(services, tb.var(pv), tb.func(skolem)));	
			services.getNamespaces().functions().addSafely(skolem);
		}
		
		if (anonUpdate.op() != UpdateJunctor.SKIP) {
			formulaToAnonymize = tb.apply(anonUpdate, formulaToAnonymize);
		}
		
		return formulaToAnonymize;
	}

}
