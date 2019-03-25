package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;

public class CBInstantiation {

    private Term formula;
    private Sequent sequent;
    private CBInstantiation result;

    private CBInstantiation(Term formula, Sequent sequent, Services services) {
        // TODO
    }

    public static CBInstantiation create(Term formula, Sequent sequent, Services services) {
        return new CBInstantiation(formula, sequent, services);
    }

    public Iterator<Term> getSubstitution() {
        return null;
    }

}
