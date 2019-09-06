package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.conflictbasedinst.EquivalenceClosure.EquivalenceClass;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

/**
 * An instantiation that aims to find instances of quantified formulas that lead
 * directly to ground conflicts so that a close rule can be applied to the
 * sequent.
 *
 * The strategy creates a set of terms that are ground within the sequent which
 * is called "context". Ground terms of the antecedent are added as they are,
 * terms of the succedent are negated. That way a conflict with the context will
 * lead to false in the antecedent or true in the succedent. Both cases allow a
 * close rule in the next rule application.
 *
 * This strategy can be adjustet with KeY-Settings. If the CBI-Mode is set to
 * CONFLICTING_ONLY cbi will only return instances that suffice to apply a close
 * rule on the sequent. If CONFLICT_INDUCING mode is enabled cbi also returns
 * instances that have a good chance to lead to conflicts.
 *
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public class ConflictBasedInstantiationOld implements TermGenerator {

    /*
     * SINGLETON BEHAVIOR
     */

    /**
     * A class to hold the singleton instance of
     * {@link ConflictBasedInstantiationOld}.
     *
     * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
     *
     */
    private static class Holder {
        private static final ConflictBasedInstantiationOld INSTANCE = new ConflictBasedInstantiationOld();
    }

    /**
     * Empty constructor for singleton creation.
     */
    private ConflictBasedInstantiationOld() {
    }

    /**
     * Returns this instantiation strategies singleton instance.
     *
     * @return This singletons instance
     */
    public static ConflictBasedInstantiationOld getInstance() {
        return Holder.INSTANCE;
    }

    /*
     * TERMGENERATOR BEHAVIOR
     */

    /**
     * The last quantified formula that were instantiated by this strategy.
     */
    private Term lastFormula;

    /**
     * The last sequent on which a formula was instantiated by this strategy.
     */
    private Sequent lastSequent;

    /**
     * The result of the last run with <code>lastFormula</code> and <code>lastSequent</code>.
     */
    private LinkedHashSet<Term> result;

    /**
     * Finds instances for the quantified formula at <code>pos</code>, if not
     * already done, and returns an iterator over terms to instantiate the
     * formula with.
     *
     * A fresh iterator of the same result set will be returned if the
     * corresponding formula was already instantiated on the sequent before.
     */
    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos,
            Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";
        System.out.println("Calling CBI generate");
        final Term formula = pos.sequentFormula().formula();
        final Sequent sequent = goal.sequent();
        final Services services = goal.proof().getServices();
        synchronized (ConflictBasedInstantiationOld.class) {
            if (formula == lastFormula && sequent == lastSequent) {
                result = new LinkedHashSet<Term>();
                return result.iterator();
            }
            lastFormula = formula;
            lastSequent = sequent;
            instantiate(formula, sequent, services);
            return result.iterator();
        }
    }

    /*
     * Services
     */
    private Services services;
    private TermBuilder tb;
    private TermFactory tf;

    /*
     * Context
     */
    private LinkedHashSet<Term> context;
    private HashMap<Operator, HashSet<Term>> contextFunctionMap;

    /*
     * Flattened formula
     */
    private Term flatBody;
    private LinkedHashSet<Constraint> constraints;
    private LinkedHashSet<Term> variables; // TODO devide in X (quantifiedvars)
    // and Y (freshvars)
    private LinkedHashSet<Term> freshVariables;

    /*
     * Conflicting Instance Substitutions
     */
    private LinkedHashSet<Term> conflictingSubstitutions = new LinkedHashSet<Term>();
    private LinkedHashSet<Term> inducingSubstitutions = new LinkedHashSet<Term>();

    /*
     * Constrained Assignments
     */
    private LinkedHashSet<LinkedHashSet<Term>> falsifyConstraints;
    private LinkedHashSet<Term> matchingConstraints;

    private void instantiate(Term formula, Sequent sequent, Services services) {
        System.out.print("CBI Instantiating: " + LogicPrinter.quickPrintTerm(formula, services));
        assert formula.op() == Quantifier.ALL : "Can only instantiate universally quantified formulae";
        this.services = services;
        tb = services.getTermBuilder();
        tf = services.getTermFactory();
        context = getGroundLiterals(sequent);
        contextFunctionMap = createFunctionMap(context);
        // System.out.println("Sequent:\n" +
        // LogicPrinter.quickPrintSequent(sequent, services));
        // System.out.println("Formula:\n" +
        // LogicPrinter.quickPrintTerm(formula, services));
        // System.out.println("Context: " + context.toString());
        variables = new LinkedHashSet<Term>();
        freshVariables = new LinkedHashSet<Term>();
        constraints = new LinkedHashSet<Constraint>();
        formula.boundVars().forEach(bv -> variables.add(tb.var(bv)));
        FlattenResult fr = flatten(formula.sub(0));
        // System.out.println("Variables: " + variables.toString());
        // System.out.println("Fresh Variables: " + freshVariables.toString());
        // System.out.println("Constraints: " + constraints.toString());
        flatBody = fr.getTerm();
        // System.out.println("Flat Body: " + flatBody.toString());
        falsifyConstraints = falsify(flatBody, true);
        // System.out.println("Falsify: " + falsifyConstraints.toString());
        matchingConstraints = matchConstraintSet(constraints);
        // System.out.println("Match: " + matchingConstraints.toString());
        extractConflictingSubstitution();
        System.out.println("Result: ");
        result.forEach(term -> System.out.print(term.toString() + ", "));
        System.out.println();
    }

    public boolean solved(PosInOccurrence pos, Goal goal) {
        final Term formula = pos.sequentFormula().formula();
        synchronized (ConflictBasedInstantiationOld.class) {
            if (result != null && !result.isEmpty() && formula == lastFormula) {
                System.out.println("cbi already has result: " + result.toString());
                return true;
            }
            return false;
        }
    }

    /*
     * BUILDING CONTEXT
     */

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
            return isGround(term.sub(0));
        return isGround(term);
    }

    /*
     * CREATING FLAT FORM
     */

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
            subsVar &= isAnyVariable(fr.getTerm());
            subs[i] = fr.getTerm();
        }
        term = tf.createTerm(term.op(), subs, term.boundVars(), null);

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
        assert isNullary(
                term) : "Can only determine flattness of term if arity is 0";

                // Predicates with arity 0 are flat by definition
                if (term.sort() == Sort.FORMULA)
                    return new FlattenResult(term, true);

                // Variables are not Ground -> not Flat
                if (isAnyVariable(term))
                    return new FlattenResult(term, false);

                // Everything else must be replaced by a fresh variable
                return replace(term);
    }

    private FlattenResult replace(Term term) {
        Term fresh = freshVariable(term.sort());
        freshVariables.add(fresh);
        constraints.add(new Constraint(fresh, term, tb));
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
            if (satisfied(term) == b) {
                return ret;
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
                return caunion(falsify(term.sub(0), b),
                        falsify(term.sub(1), b));
            }
            else {
                return union(falsify(term.sub(0), b), falsify(term.sub(1), b));
            }
        }
        ret.add(new LinkedHashSet<Term>());
        return ret;
    }

    private LinkedHashSet<Term> createAssignment(Term term) {
        LinkedHashSet<Term> ret = new LinkedHashSet<Term>();
        ret.add(term);
        return ret;
    }

    /*
     * MATCH
     */

    private LinkedHashSet<Term> matchConstraintSet(
            LinkedHashSet<Constraint> constraints) {
        LinkedHashSet<Term> matchedConstraints = new LinkedHashSet<Term>();
        for (Constraint constraint : constraints) {
            getMatches(constraint, matchedConstraints);
        }
        return matchedConstraints;
    }

    private void getMatches(Constraint constraint,
            LinkedHashSet<Term> matches) {
        HashSet<Term> cfun = contextFunctionMap.get(constraint.getTerm().op());
        if (cfun == null)
            return;
        for (Term match : cfun) {
            if (match.arity() == constraint.getTerm().arity()) {
                matches.add(tb.equals(constraint.getVar(), match));
                for (int i = 0; i < match.arity(); i++) {
                    matches.add(tb.equals(constraint.getTerm().sub(i),
                            match.sub(i)));
                }
            }
        }
    }

    /*
     * EXTRACT CONFLICTING SUBSTITUTION
     */

    private void extractConflictingSubstitution() {
        // System.out.println("Number of falsify constraints: " +
        // falsifyConstraints.size());
        for (LinkedHashSet<Term> fca : falsifyConstraints) {
            LinkedHashSet<Term> b = new LinkedHashSet<Term>();
            LinkedHashSet<Term> c = new LinkedHashSet<Term>();
            EquivalenceClosure ec = new EquivalenceClosure();

            // splitting into a and b
            for (Term term : union(matchingConstraints, fca)) {
                if (ec.addEquality(term)) {
                    b.add(term);
                }
                else {
                    c.add(term);
                }
            }
            // System.out.println("EQClosure: " + ec.toString());
            LinkedHashSet<Term> groundSubst = new LinkedHashSet<Term>();
            Term subst = tb.and(c);
            for (EquivalenceClass eqc : ec.getEquivalenceClasses()) {
                // System.out.println("Checking eqc: " + eqc.toString());
                if (eqc.containsGround()) {
                    Term grnd = eqc.getGroundTerm();
                    // System.out.println("Ground Term: " + grnd.toString());
                    for (Term term : eqc) {
                        if (!(term.equals(grnd))) {
                            QuantifiableVariable qv = (QuantifiableVariable) term
                                    .op();
                            subst = tb.subst(qv, grnd, subst);
                            if (isVariable(term)) {
                                // System.out.println("Adding GroundSubst: " +
                                // grnd.toString());
                                groundSubst.add(grnd);
                            }
                        }
                    }
                }
                else {
                    // TODO take arbitrary terms from context
                }
            }
            result = new LinkedHashSet<Term>();
            // System.out.println("subst: " + subst.toString());
            if (satisfied(subst)) {
                conflictingSubstitutions.addAll(groundSubst);
                result.addAll(groundSubst);
            }
            else {
                inducingSubstitutions.addAll(groundSubst);
                result.addAll(groundSubst);
            }
        }

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

    private boolean isFreshVariable(Term term) {
        return freshVariables.contains(term);
    }

    private boolean isAnyVariable(Term term) {
        return isFreshVariable(term) || isVariable(term);
    }

    private boolean isNullary(Term term) {
        return term.arity() == 0;
    }

    private final String BASENAME = "cbi";
    private int varcnt = 0;

    private Term freshVariable(Sort sort) {
        return tb.var(
                new LogicVariable(new Name(BASENAME + "_" + ++varcnt), sort));
    }

    private Term negate(Term term) {
        return tb.not(term);
    }

    private boolean isGround(Term term) {
        // if (isNullary(term)) {
        // return (!variables.contains(term));
        // }
        // for (Term sub : term.subs()) {
        // if (!isGround(sub))
        // return false;
        // }
        // return true;
        if (isNullary(term)) {
            return (term.freeVars().size() == 0);
        }
        for (Term sub : term.subs()) {
            if (!isGround(sub))
                return false;
        }
        return true;

    }

    private LinkedHashSet<LinkedHashSet<Term>> caunion(
            LinkedHashSet<LinkedHashSet<Term>> a,
            LinkedHashSet<LinkedHashSet<Term>> b) {
        LinkedHashSet<LinkedHashSet<Term>> ret = new LinkedHashSet<LinkedHashSet<Term>>();
        a.forEach(s -> b.forEach(t -> {
            ret.add(union(s, t));
        }));
        return ret;
    }

    private <T> LinkedHashSet<T> union(LinkedHashSet<T> s, LinkedHashSet<T> t) {
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
        // System.out.println(context.toString()
        // + (sat ? " satisfies " : " not satisfies ") + term.toString());
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

    private static HashMap<Operator, HashSet<Term>> createFunctionMap(
            LinkedHashSet<Term> context) {
        HashMap<Operator, HashSet<Term>> ret = new HashMap<Operator, HashSet<Term>>();
        for (Term term : context) {
            addTermToFunctionSet(term, ret);
        }
        return ret;
    }

    private static void addTermToFunctionSet(Term term,
            HashMap<Operator, HashSet<Term>> ret) {
        if (ret.containsKey(term.op())) {
            ret.get(term.op()).add(term);
            term.subs().forEach(t -> addTermToFunctionSet(t, ret));
        }
        else {
            ret.put(term.op(), new HashSet<Term>());
            addTermToFunctionSet(term, ret);
        }
    }
}
