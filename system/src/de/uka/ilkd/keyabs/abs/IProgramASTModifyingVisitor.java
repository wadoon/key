package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.ProgramElement;

public interface IProgramASTModifyingVisitor {

    public abstract void start();
    
    public abstract ProgramElement result();

}