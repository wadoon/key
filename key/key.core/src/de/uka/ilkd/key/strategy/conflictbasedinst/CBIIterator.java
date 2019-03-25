package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

public class CBIIterator implements Iterator<Term>{
    private final Iterator<Term> instances;
    private final QuantifiableVariable quantifiableVariable;
    private final TermServices services;

    protected CBIIterator(Iterator<Term> instances, QuantifiableVariable quantifiableVariable, TermServices services) {
        this.instances = instances;
        this.quantifiableVariable = quantifiableVariable;
        this.services = services;
    }

    @Override
    public boolean hasNext() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public Term next() {
        // TODO Auto-generated method stub
        return null;
    }
}