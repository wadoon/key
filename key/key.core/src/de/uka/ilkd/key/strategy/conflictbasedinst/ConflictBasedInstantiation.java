package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class ConflictBasedInstantiation {

    private Services services;
    private TermBuilder tb;
    private TermFactory tf;
    private LinkedHashSet<LinkedHashSet<Term>> fCA;
    private LinkedHashSet<LinkedHashSet<Term>> mCA;
    private LinkedHashSet<LinkedHashSet<Term>> cCA;

    public ConflictBasedInstantiation(Term formula, Sequent sequent,
            Services services) {
        assert formula.op() == Quantifier.ALL : "Can only instantiate universally quantified formulae";
        this.services = services;
        tb = services.getTermBuilder();
        tf = services.getTermFactory();
        context = getGroundLiterals(sequent);
        System.out.println("Context: " + context.toString());
        variables = new LinkedHashSet<Term>();
        constraints = new LinkedHashSet<Term>();
        formula.boundVars().forEach(bv -> variables.add(tb.var(bv)));
        FlattenResult fr = flatten(formula.sub(0));
        System.out.println("Variables: " + variables.toString());
        System.out.println("Constraints: " + constraints.toString());
        flatBody = fr.getTerm();
        System.out.println("Flat Body: " + flatBody.toString());
        fCA = falsify(flatBody, true);
        System.out.println("Falsify: " + fCA.toString());
        mCA = match(constraints.iterator());
        System.out.println("Match: " + mCA.toString());
    }

    public LinkedHashSet<Term> getInstantiation() {
        return new LinkedHashSet<Term>();
    }

    /*
     * BUILDING CONTEXT
     */

    private LinkedHashSet<Term> context;

    private LinkedHashSet<Term> getGroundLiterals(Sequent sequent) {
        LinkedHashSet<Term> ret = new LinkedHashSet<Term>();
        ret.addAll(getGroundLiterals(sequent.antecedent(), true));
        ret.addAll(getGroundLiterals(sequent.succedent(), false));
        return ret;
    }

    private LinkedHashSet<Term> getGroundLiterals(Semisequent semiseq,
            boolean b) {
        LinkedHashSet<Term> ret = new LinkedHashSet<Term>();
        for (SequentFormula sf : semiseq) {
            Term term = sf.formula();
            if (isGroundLiteral(term)) {
                ret.add(b ? term : negate(term));
            }
        }
        return ret;
    }

    private boolean isGroundLiteral(Term term) {
        if (term.op() == Junctor.NOT)
            return isGroundLiteral(term.sub(0));
        return isAtom(term);
    }

    /*
     * CREATING FLAT FORM
     */

    private Term flatBody;
    private LinkedHashSet<Term> constraints;
    private LinkedHashSet<Term> variables;

    private FlattenResult flatten(Term term) {
        /*
         * first handle quantifiers because all recursive calls on sub-terms
         * must know possible substitutions
         */
        // if (term.op() instanceof Quantifier) {
        // term = handleQuantifier(term, (Quantifier) term.op());
        // }

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
        assert isNullary(term) : "Can only determine if term is flat if arity is 0";

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
        Term fresh = freshVariable(term.sort());
        variables.add(fresh);
        constraints.add(tb.equals(fresh, term));
        // Variables are not flat
        return new FlattenResult(fresh, false);
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

    /*
     * FALSIFY
     */

    private LinkedHashSet<LinkedHashSet<Term>> falsify(Term term, boolean b) {
        LinkedHashSet<LinkedHashSet<Term>> ret = new LinkedHashSet<LinkedHashSet<Term>>();
        if (isGround(term)) {
            if(satisfied(term) != b) {
                return ret;
            } else {
                // TODO maybe exit with exception?
                return null;
            }
        }

        if (term.op() == Equality.EQUALS) {
            ret.add(createAssignment(b ? negate(term) : term));
            return ret;
        }

        if (term.op() == Junctor.NOT) {
            return falsify(term.sub(0), !b);
        }

        if (term.op() == Junctor.OR) {
            if (b) {
                return caunion(falsify(term.sub(0), b), falsify(term.sub(1), b));
            } else {
                return union(falsify(term.sub(0), b), falsify(term.sub(1), b));
            }
        }
        return ret;
    }

    public LinkedHashSet<Term> createAssignment(Term term) {
        LinkedHashSet<Term> ret = new LinkedHashSet<Term>();
        ret.add(term);
        return ret;
    }

    /*
     * MATCH
     */

    private LinkedHashSet<LinkedHashSet<Term>> match(Iterator<Term> it) {
        LinkedHashSet<LinkedHashSet<Term>> ret = new LinkedHashSet<LinkedHashSet<Term>>();
        if(!it.hasNext()) return ret;
        Term term = it.next();
        if (isConstraint(term)) {
            return caunion(getMatches(term), match(it));
        }
        else {
            return ret;
        }
    }

    private LinkedHashSet<LinkedHashSet<Term>> getMatches(Term term) {
        LinkedHashSet<LinkedHashSet<Term>> ret = new LinkedHashSet<LinkedHashSet<Term>>();
        for (Term c : context) {
            ret.add(matches(term, c));
        }
        return ret;
    }

    private LinkedHashSet<Term> matches(Term term, Term c) {
        LinkedHashSet<Term> ret = new LinkedHashSet<Term>();
        if (c.op() == term.sub(1).op()) {
            ret.add(tb.equals(term.sub(0), c));
            for (int i = 0; i < c.arity(); i++) {
                ret.add(tb.equals(term.sub(1).sub(i), c.sub(i)));
            }
        }
        for (Term sub : c.subs()) {
            ret.addAll(matches(term, sub));
        }
        return ret;
    }

    /*
     * UTILITY
     */

    private boolean isAtom(Term term) {
        // TODO ask Richard maby
        return term.op() == Equality.EQUALS;
    }

    private boolean isVariable(Term term) {
        return variables.contains(term);
    }

    private boolean isNullary(Term term) {
        return term.arity() == 0;
    }

    private static final String BASENAME = "cbi";
    private int varcnt = 0;

    private Term freshVariable(Sort sort) {
        return tb.var(new LogicVariable(new Name(BASENAME + "_" + ++varcnt), sort));
    }

    private Term negate(Term term) {
        return tb.not(term);
    }

    private boolean isGround(Term term) {
        if (isNullary(term)) {
            return (!variables.contains(term));
        }
        for (Term sub : term.subs()) {
            if (!isGround(sub))
                return false;
        }
        return true;
    }

    private boolean isConstraint(Term term) {
        if (term.op() != Equality.EQUALS)
            return false;
        if (term.sub(1).op() instanceof Function) {
            return true;
        }
        return false;
    }

    private LinkedHashSet<LinkedHashSet<Term>> caunion(LinkedHashSet<LinkedHashSet<Term>> a, LinkedHashSet<LinkedHashSet<Term>> b) {
        LinkedHashSet<LinkedHashSet<Term>> ret = new LinkedHashSet<LinkedHashSet<Term>>();
        a.forEach(s -> b.forEach(t -> {
            ret.add(union(s,t));
        }));
        return ret;
    }

    private <T> LinkedHashSet<T> union(LinkedHashSet<T> s,
            LinkedHashSet<T> t) {
        LinkedHashSet<T> ret = new LinkedHashSet<T>();
        ret.addAll(s);
        ret.addAll(t);
        return ret;
    }

    private static final String SUBPROOF = "CBI_SUBPROOF";
    private static final long timeoutInMillis = Long.MAX_VALUE;
    private static final int maxRuleApps = Integer.MAX_VALUE;

    private boolean satisfied(Term term) {
        if (services.getProof().name().toString().startsWith(SUBPROOF)) {
            System.out.println("Satisfied was chain-called");
            return false;
        }
        Semisequent ante = new Semisequent(new SequentFormula(tb.and(context)));
        Semisequent succ = new Semisequent(new SequentFormula(term));
        Sequent seq = Sequent.createSequent(ante, succ);

        final ProofStarter ps = new ProofStarter(false);
        final ProofEnvironment env = SideProofUtil
                .cloneProofEnvironmentWithOwnOneStepSimplifier(
                        services.getProof());
        try {
            ps.init(seq, env, SUBPROOF);
        }
        catch (ProofInputException pie) {
            pie.printStackTrace();
            return false;
        }

        final StrategyProperties sp = setupStrategy();

        ps.setStrategyProperties(sp);
        ps.setMaxRuleApplications(maxRuleApps);
        ps.setTimeout(timeoutInMillis);
        final ApplyStrategyInfo info = ps.start();

        boolean sat = info.getProof().closed();
        System.out.println(context.toString()
                + (sat ? " satisfies " : " not satisfies ") + term.toString());
        return sat;
    }

    protected StrategyProperties setupStrategy() {
        final StrategyProperties sp = new StrategyProperties();
        sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY,
                StrategyProperties.AUTO_INDUCTION_OFF);
        sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                StrategyProperties.QUERY_OFF);
        sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
                StrategyProperties.QUANTIFIERS_NONE);
        sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY,
                StrategyProperties.SPLITTING_NORMAL);
        sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
                StrategyProperties.DEP_OFF);
        sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY,
                StrategyProperties.CLASS_AXIOM_OFF);
        return sp;
    }
}
