package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class ConcreteABS2KeYABSConverter extends AbstractABS2KeYABSConverter {

    private final Namespace progVars;
    
    public ConcreteABS2KeYABSConverter(Namespace varns, IServices services) {
        super(services);
        this.progVars = varns;
    }

    @Override
    protected IProgramVariable lookupLocalVariable(String name) {
        return (IProgramVariable) progVars.lookup(new Name(name));
    }

    @Override
    protected IProgramVariable lookupFieldVariable(String name) {
        return (IProgramVariable) progVars.lookup(new Name(name));
    }

 
}
