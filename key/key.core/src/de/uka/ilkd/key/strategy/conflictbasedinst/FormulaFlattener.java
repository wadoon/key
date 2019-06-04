package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedHashSet;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.ProofSaver;

public class FormulaFlattener {

    /** The services to build new terms with */
    private Services services;
    /** Shortcut to termbuilder */
    private TermBuilder tb;
    /** Shortcut to termfactory */
    private TermFactory tf;
    /** The Set of variables */
    LinkedHashSet<QuantifiableVariable> vars;
    /** The set of constraints */
    LinkedHashSet<Term> constraints;

    private int i = 0;
    private static final String basename = "cbfv";

    private FormulaFlattener(Services services,
            ImmutableArray<QuantifiableVariable> topVars) {
        this.services = services;
        this.tb = this.services.getTermBuilder();
        this.tf = this.services.getTermFactory();
        this.vars = new LinkedHashSet<QuantifiableVariable>();
        for (QuantifiableVariable qv : topVars) {
            vars.add(qv);
        }
        this.constraints = new LinkedHashSet<Term>();
    }

    public static FlatQuantifiedFormula flatten(Term term, Services services) {
        assert term
        .op() == Quantifier.ALL : "Can only flat terms that are all-quantified at top level.";

        FormulaFlattener fqff = new FormulaFlattener(services,
                term.boundVars());

        System.out.println("Flatten: " + ProofSaver.printTerm(term, services));

        FlattenResult fr = fqff.flatten(term.sub(0));
        if (!fr.isFlat())
            /* TODO this is an exception */;

        FlatQuantifiedFormula fqf = new FlatQuantifiedFormula(fr.getTerm(),
                fqff.getVars(), fqff.getConstraints());

        return fqf;
    }

    private LinkedHashSet<QuantifiableVariable> getVars() {
        return vars;
    }

    private LinkedHashSet<Term> getConstraints() {
        return constraints;
    }

    private FlattenResult flatten(Term term) {
        /*
         * first handle quantifiers because all recursive calls on sub-terms
         * must know possible substitutions
         */
        if (term.op() instanceof Quantifier) {
            term = handleQuantifier(term, (Quantifier) term.op());
        }

        /*
         * Terms with arity 0 can be handled without flatten its sub-terms.
         */
        if (term.arity() == 0) {
            return handleNullary(term);
        }

        return flattenSubs(term);
    }

    private FlattenResult flattenSubs(Term term) {
        int arity = term.arity();
        assert (arity != 0) : "Cannot flatten subs if arity 0";

        Term[] subs = new Term[arity];
        boolean subsFlat = true;
        boolean subsVar = true;
        for (int i = 0; i < arity; i++) {
            FlattenResult fr = flatten(term.sub(i));
            subsFlat &= fr.isFlat();
            subsVar &= isVariable(fr.getTerm());
            subs[i] = fr.getTerm();
        }

        term = tf.createTerm(term.op(), subs);

        // a junction of flat terms is flat
        if (subsFlat && term.op() instanceof Junctor) {
            return new FlattenResult(term, true);
        }
        // an equality between variables is flat
        if (subsVar && term.op() == Equality.EQUALS) {
            return new FlattenResult(term, true);
        }

        // everything else is not
        return replace(term);

    }

    private FlattenResult handleNullary(Term term) {
        assert term
        .arity() == 0 : "Can only determine if term is flat if arity is 0";

        // Predicates with arity 0 are flat by definition
        if (term.sort() == Sort.FORMULA)
            return new FlattenResult(term, true);

        // Variables are not Ground -> not Flat
        if (isVariable(term))
            return new FlattenResult(term, false);

        // Everything else must be replaced by a fresh variable
        return replace(term);
    }

    private FlattenResult replace(Term term) {
        LogicVariable fresh = freshVariable(term.sort());
        addVariable(fresh);
        Term freshTerm = tb.var(fresh);
        Term constraint = tb.equals(freshTerm, term);
        addConstraint(constraint);
        // Variables are not flat
        return new FlattenResult(freshTerm, false);
    }

    private void addVariable(LogicVariable fresh) {
        vars.add(fresh);
    }

    private void addConstraint(Term constraint) {
        constraints.add(constraint);
    }

    private Term handleQuantifier(Term term, Quantifier quant) {
        /*
         * TODO think about extending the algorithm to flat formulas with inner
         * quantifiers.
         */
        throw new UnsupportedQuantifierException(quant);
    }

    private LogicVariable freshVariable(Sort sort) {
        return new LogicVariable(new Name(basename + "_" + ++i), sort);
    }

    private boolean isVariable(Term term) {
        return vars.contains(term.op());
    }

    private class FlattenResult {
        private Term term;
        private Boolean flat;

        public FlattenResult(Term term, Boolean ground) {
            super();
            this.setTerm(term);
            this.setFlat(ground);
        }

        public Term getTerm() {
            return term;
        }

        public void setTerm(Term term) {
            this.term = term;
        }

        public Boolean isFlat() {
            return flat;
        }

        public void setFlat(Boolean flat) {
            this.flat = flat;
        }

    }

}
