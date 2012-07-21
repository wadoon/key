package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class SchemaABS2KeYABSConverter extends AbstractABS2KeYABSConverter {

    
    private final Namespace schemaVariables;

    public SchemaABS2KeYABSConverter(Namespace schemaVariables) {
        this.schemaVariables = schemaVariables;
    }
    
    IProgramVariable lookup(String name) {
        return (IProgramVariable) schemaVariables.lookup(new Name(name));
    }

    @Override
    protected IProgramVariable lookupLocalVariable(String name) {
        return lookup(name);
    }

    @Override
    protected IProgramVariable lookupFieldVariable(String name) {
        return lookup(name);
    }

}
