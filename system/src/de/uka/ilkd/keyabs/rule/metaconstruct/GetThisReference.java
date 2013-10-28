package de.uka.ilkd.keyabs.rule.metaconstruct;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class GetThisReference extends AbstractTermTransformer {

    public GetThisReference() {
	super(new Name("#this"), 0);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, IServices services) {
    	return services.getTermBuilder().
		func((Function) services.getNamespaces().functions().lookup(new Name("this")));
    }

}
