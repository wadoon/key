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
        int i = 0;
        System.out.println("Print all instances.");
        while(this.instances.hasNext()) {
            i++;
            System.out.println("Instance " + i + ": " + this.instances.next().toString());
        }
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