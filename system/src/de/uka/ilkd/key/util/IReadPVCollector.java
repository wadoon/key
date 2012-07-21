package de.uka.ilkd.key.util;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.visitor.ProgramVisitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public interface IReadPVCollector extends ProgramVisitor {

    void start();

    ImmutableSet<ProgramVariable> result();

}
