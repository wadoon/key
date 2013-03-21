package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class ConcreteABS2KeYABSConverter extends AbstractABS2KeYABSConverter {

    public ConcreteABS2KeYABSConverter(Namespace<IProgramVariable> varns,
            IServices services) {
        super(services, varns);
    }

    @Override
    protected IProgramVariable lookupLocalVariable(String name) {
        return pv.lookup(new Name(name));
    }

    @Override
    protected IProgramVariable lookupFieldVariable(String className, String name) {
        return pv.lookup(new ProgramElementName(name, className));
    }

}
