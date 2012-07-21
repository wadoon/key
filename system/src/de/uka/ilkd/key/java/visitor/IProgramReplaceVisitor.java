package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.ProgramElement;

public interface IProgramReplaceVisitor {

    /** starts the walker*/
    public abstract void start();

    public abstract ProgramElement result();

}