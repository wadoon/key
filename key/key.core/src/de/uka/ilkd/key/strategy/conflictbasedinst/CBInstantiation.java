package de.uka.ilkd.key.strategy.conflictbasedinst;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Quantifier;

public class CBInstantiation {

    private Term formula;
    private Sequent sequent;
    private CBInstantiation result;
    private Services services;

    private ImmutableSet<Term> constrainedAssignments;
    private ImmutableSet<Term> context;

    private CBInstantiation(Term formula, Sequent sequent, Services services) {
        this.formula = formula;
        this.sequent = sequent;
        this.services = services;
        constrainedAssignments = DefaultImmutableSet.<Term>nil();
        context = DefaultImmutableSet.<Term>nil();
        addToContext(sequent);
    }

    private void addToContext(Sequent seq) {
        seq.antecedent().asList().forEach(e -> addToContext(e.formula()));
        seq.succedent().asList().forEach(e -> addToContext(services.getTermBuilder().not(e.formula())));
        System.out.println("*** Adding Antecedent ***");
        for(final SequentFormula sf: seq.antecedent()) {
            System.out.println("Propose: " + sf.formula().toString());
            addToContext(sf.formula());
        }
        System.out.println("*** Adding Succedent ***");
        for(final SequentFormula sf: seq.succedent()) {
            System.out.println("Propose: " + sf.formula().toString());
            addToContext(services.getTermBuilder().not(sf.formula()));
        }

    }

    private void addToContext(Term t) {
        if(isGroundLiteral(t)) {
            System.out.println("operator: " + t.op().toString());
            System.out.println("Adding: " + t.toString());
            context.add(t);
        }else {
            System.out.println("Not Adding: " + t.toString());
        }
    }

    private boolean isGroundLiteral(Term t) {
        return isGround(t) && isLiteral(t);
    }

    private void flat(Term formula2, Services services) {
        TermFactory tf = new TermFactory();
        TermBuilder tb = new TermBuilder(tf, services);
    }

    private boolean isGround(Term t) {
        return !isQuantified(t);
    }

    private boolean isQuantified(Term t) {
        if(t.op() instanceof Quantifier) {
            System.out.println("Quantified: " + t.toString());
            return true;
        }
        return isQuantified(t.subs());
    }

    private boolean isQuantified(ImmutableArray<Term> subs) {
        for(Term sub: subs) {
            if(isQuantified(sub)) return true;
        }
        return false;
    }

    private boolean isLiteral(Term t) {
        return false;
    }

    public static CBInstantiation create(Term formula, Sequent sequent, Services services) {
        System.out.println("Sequent: " + sequent.toString());
        return new CBInstantiation(formula, sequent, services);
    }

    public ImmutableSet<Term> getSubstitution() {
        ImmutableSet<Term> res = DefaultImmutableSet.<Term> nil();
        //TODO fill set of substitutions
        return res;
    }

}
