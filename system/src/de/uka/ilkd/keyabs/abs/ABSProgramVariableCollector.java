package de.uka.ilkd.keyabs.abs;

import java.util.HashSet;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.IProgramVariableCollector;
import de.uka.ilkd.key.logic.op.LocationVariable;

public class ABSProgramVariableCollector extends ABSVisitorImpl implements
        IProgramVariableCollector<LocationVariable> {

    private HashSet<LocationVariable> result = new HashSet<LocationVariable>();

    public ABSProgramVariableCollector(ProgramElement root, ABSServices services) {
        super(root);
    }

    @Override
    public void start() {
        walk(root());
    }

    @Override
    public HashSet<LocationVariable> result() {
        return result;
    }

    @Override
    public String toString() {
        return result.toString();
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
        result.add(x);
    }


}
