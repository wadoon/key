package de.uka.ilkd.key.java.visitor;

import java.util.HashSet;

import de.uka.ilkd.key.java.ProgramElement;

public interface IProgramVariableCollector<S extends ProgramElement> {
    
    void start();
    HashSet<S> result();
}
