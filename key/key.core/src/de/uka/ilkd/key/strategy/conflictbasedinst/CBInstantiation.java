package de.uka.ilkd.key.strategy.conflictbasedinst;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;

public class CBInstantiation {

    private Term formula;
    private Sequent sequent;
    private CBInstantiation result;

    private CBInstantiation(Term formula, Sequent sequent, Services services) {
        this.formula = formula;
        this.sequent = sequent;
    }

    private void flat(Term formula2, Services services) {
        TermFactory tf = new TermFactory();
        TermBuilder tb = new TermBuilder(tf, services);
    }

    private boolean isGround(Term t) {
        return t.freeVars().size() == 0;
    }

    public static CBInstantiation create(Term formula, Sequent sequent, Services services) {
        return new CBInstantiation(formula, sequent, services);
    }

    public ImmutableSet<Term> getSubstitution() {
        ImmutableSet<Term> res = DefaultImmutableSet.<Term> nil();
        //TODO fill set of substitutions
        return res;
    }

}
