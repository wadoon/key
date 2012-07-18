package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.util.ExtList;

public interface IProgramSVSort<S extends IServices> extends Sort {

    public abstract boolean canStandFor(Term t);

    public abstract boolean canStandFor(ProgramElement check,
            ExecutionContext ec, S services);

    public abstract IProgramSVSort<S> createInstance(String parameter);

    public abstract ProgramElement getSVWithSort(ExtList l, Class alternative);

}