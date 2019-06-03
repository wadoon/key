package de.uka.ilkd.key.strategy.conflictbasedinst;


import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.strategy.conflictbasedinst.DecidingTermTraverser.Condition;

public class CBInstantiation {

    private Term formula;
    private Sequent sequent;
    private CBInstantiation result;
    private Services services;

    private ImmutableSet<Term> constrainedAssignments;
    private ImmutableSet<Term> context;

    private Condition operatorIsSupported = new Condition() {

        @Override
        public boolean decide(Term t) {
            System.out.println(t.toString() + ": " + t.op().toString() + ", " + t.op().getClass().getSimpleName());
            return (t.op() instanceof Equality) || (t.op() instanceof Function);
        }

    };

    private Condition termIsGround = new Condition() {

        @Override
        public boolean decide(Term t) {
            return (t.boundVars().size() == 0);
        }
    };

    private static final String CB_INNER_PROOF = "CB_INNER_PROOF";

    private CBInstantiation(Term formula, Sequent sequent, Services services) {
        this.formula = formula;
        traverse(formula);
        this.sequent = sequent;
        this.services = services;
        this.constrainedAssignments = DefaultImmutableSet.<Term>nil();
        this.context = DefaultImmutableSet.<Term>nil();
        //FlatQuantifiedFormula flat = QuantifiedFormulaFlattener.flatten(formula, services);
    }

    private void traverse(Term term) {
        System.out.println(ProofSaver.printTerm(term, services)
                + " boundVars: " + term.boundVars().toString()
                + " freeVars: " + term.freeVars().toString()
                + " subs: " + term.subs().toString()
                + " sort: " + term.sort().toString());
        term.subs().forEach(sub -> traverse(sub));
    }

    private void addToContext(Sequent seq) {
        System.out.println("*** Adding Antecedent ***");
        seq.antecedent().asList().forEach(e -> addToContext(e.formula(), true));
        System.out.println("*** Adding Succedent ***");
        seq.succedent().asList().forEach(e -> addToContext(e.formula(), false));
        System.out.println("Context: " + context.toString());
    }

    private void addToContext(Term t, boolean b) {
        System.out.println("Deciding: " + t.toString());
        if(t.op() == Quantifier.ALL) {
            System.out.println("QV: " + t.boundVars().get(0));
        }
        if(DecidingTermTraverser.decide(t, operatorIsSupported)) {
            Term term = b ? t : services.getTermBuilder().not(t);
            System.out.println("Adding: " + term);
            context = context.add(term);
        }
    }

    private boolean isQuantified(Term t) {
        if(t.op() instanceof Quantifier) {
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

    public static CBInstantiation create(Term formula, Sequent sequent, Services services) {
        System.out.println("Sequent: " + sequent.toString());
        return new CBInstantiation(formula, sequent, services);
    }

    private ImmutableSet<ImmutableSet<Term>> falsify(Term term, boolean b) {
        ImmutableSet<ImmutableSet<Term>> ret = DefaultImmutableSet.<ImmutableSet<Term>>nil();
        System.out.println("Falsify: " + term.toString());
        if(isGround(term)) {
            System.out.println("\tisGround.");
            if(satisfied(term) == b) {
                System.out.println("\tisSatisfied. Returning {{}}");
                return ret.add(DefaultImmutableSet.<Term>nil());
            }else {
                System.out.println("\tisNotSatisfied. Returning {}");
                return ret;
            }
        }

        if(term.op() == Equality.EQUALS)  {
            System.out.println("\tisEquals.");
            return ret.add(DefaultImmutableSet.<Term>nil().add(b ? negate(term) : term));
        }

        if(term.op() == Junctor.NOT) {
            System.out.println("\tisNot.");
            return falsify(term.sub(0), !b);
        }

        if(term.op() == Junctor.OR) {
            System.out.println("\tisOR.");
            if(b) {
                ImmutableSet<ImmutableSet<Term>> partial = falsify(term.sub(0), b);
                for(ImmutableSet<Term> t: falsify(term.sub(1), b)) {
                    for(ImmutableSet<Term> u: partial) {
                        ImmutableSet<Term> unit = t.union(u);
                        ret = ret.add(unit);
                    }
                }
                return ret;
            }else {
                ret = falsify(term.sub(0), b);
                ret = ret.union(falsify(term.sub(1), b));
                return ret;
            }
        }
        return ret;
    }

    private ImmutableSet<ImmutableSet<Term>> unite(
            ImmutableSet<ImmutableSet<Term>> partials,
            ImmutableSet<ImmutableSet<Term>> falsify) {
        // TODO Auto-generated method stub
        return null;
    }

    private Term negate(Term term) {
        return services.getTermBuilder().not(term);
    }

    private boolean satisfied(Term term) {
        return false;
    }

    private boolean isGround(Term term) {
        return DecidingTermTraverser.decide(term, termIsGround);
    }

    public ImmutableSet<Term> getSubstitution() {
        if(services.getProof().name().toString().startsWith(CB_INNER_PROOF)) {
            return DefaultImmutableSet.<Term>nil();
        }
        addToContext(sequent);
        ImmutableSet<Term> res = DefaultImmutableSet.<Term> nil();
        System.out.println("ConstrainedAssignments: " + falsify(formula, true));
        //TODO fill set of substitutions
        return res;
    }

}
