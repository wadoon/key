package de.uka.ilkd.key.testgeneration.core.oracle;

import de.uka.ilkd.key.logic.Term;

public class Stuff<T> {

    public T doStuff() {
        return null;
    }
}

class Stuff2 extends Stuff<Term> {
    
    @Override
    public Term doStuff() {
        // TODO Auto-generated method stub
        return super.doStuff();
    }
}