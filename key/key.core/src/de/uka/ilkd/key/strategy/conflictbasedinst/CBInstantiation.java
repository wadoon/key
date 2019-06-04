package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.HashSet;
import java.util.LinkedHashSet;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.conflictbasedinst.DecidingTermTraverser.Condition;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class CBInstantiation {

    private static final String SUBPROOF = "CBI_SUBPROOF";
    private static final int maxRuleApps = 0;
    private static final long timeoutInMillis = 0;

    private Term formula;
    private Sequent sequent;
    private Services services;
    private TermBuilder tb;

    private ImmutableSet<Term> context;
    private LinkedHashSet<QuantifiableVariable> variables;

    private Condition operatorIsSupported = new Condition() {

        @Override
        public boolean decide(Term t) {
            return (t.op() instanceof Equality) || (t.op() instanceof Function);
        }

    };

    private Condition termIsGround = new Condition() {

        @Override
        public boolean decide(Term t) {
            return (t.boundVars().size() == 0);
        }
    };

    private CBInstantiation(Term formula, Sequent sequent, Services services) {
        this.formula = formula;
        sequent.antecedent().forEach(s -> traverse(s.formula()));
        this.sequent = sequent;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.context = DefaultImmutableSet.<Term> nil();
    }

    private void traverse(Term term) {
        System.out.println(ProofSaver.printTerm(term, services) + " boundVars: "
                + term.boundVars().toString() + " freeVars: "
                + term.freeVars().toString() + " subs: "
                + term.subs().toString() + " sort: " + term.sort().toString()
                + " op: " + term.op().toString() + " opclass: "
                + term.op().getClass().getSimpleName());
        term.subs().forEach(sub -> traverse(sub));
    }

    private void addToContext(Sequent seq) {
        seq.antecedent().asList().forEach(e -> addToContext(e.formula(), true));
        seq.succedent().asList().forEach(e -> addToContext(e.formula(), false));
        System.out.println("Context: " + context.toString());
    }

    private void addToContext(Term term, boolean b) {
        if (DecidingTermTraverser.decide(term, operatorIsSupported)) {
            term = b ? term : tb.not(term);
            context = context.add(term);
        }
    }

    public static CBInstantiation create(Term formula, Sequent sequent,
            Services services) {
        System.out.println("Sequent: " + sequent.toString());
        return new CBInstantiation(formula, sequent, services);
    }

    private HashSet<Term> falsify(Term term, boolean b) {
        HashSet<Term> ret = new HashSet<Term>();
        if (isGround(term)) {
            return ret;
        }

        if (term.op() == Equality.EQUALS) {
            ret.add(b ? negate(term) : term);
            return ret;
        }

        if (term.op() == Junctor.NOT) {
            return falsify(term.sub(0), !b);
        }

        if (term.op() == Junctor.OR) {
            if (b) {
                ret = falsify(term.sub(0), b);
                ret.addAll(falsify(term.sub(1), b));
                return ret;
            } else {
                ret = falsify(term.sub(0), b);
                ret.addAll(falsify(term.sub(1), b));
                return ret;
            }
        }
        return ret;
    }

    private Term negate(Term term) {
        return services.getTermBuilder().not(term);
    }

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

    /**
     * creates the strategy configuration to be used for the side proof
     *
     * @return the StrategyProperties
     */
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

    private boolean isGround(Term term) {
        if (term.arity() == 0 && term.op() instanceof QuantifiableVariable) {
            QuantifiableVariable qv = (QuantifiableVariable) term.op();
            return (!variables.contains(qv));
        }
        for (Term sub : term.subs()) {
            if (!isGround(sub))
                return false;
        }
        return true;
    }

    private HashSet<Term> match(Term term) {
        if (isConstraint(term)) {
            return getMatches(term);
        }
        else {
            return new HashSet<Term>();
        }
    }

    private HashSet<Term> getMatches(Term term) {
        HashSet<Term> ret = new HashSet<Term>();
        for (Term c : context) {
            ret.addAll(matches(term, c));
        }
        return ret;
    }

    private HashSet<Term> matches(Term term, Term c) {
        HashSet<Term> ret = new HashSet<Term>();
        if (c.op() == term.sub(1).op()) {
            System.out.println(
                    "Matching: " + term.toString() + " and " + c.toString());
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

    private boolean isConstraint(Term term) {
        if (term.op() != Equality.EQUALS)
            return false;
        if (term.sub(1).op() instanceof Function) {
            return true;
        }
        return false;
    }

    public ImmutableSet<Term> getSubstitution() {
        if (services.getProof().name().toString().startsWith(SUBPROOF)) {
            System.out.println("Instantiation was chain-called");
            return DefaultImmutableSet.<Term> nil();
        }
        addToContext(sequent);
        ImmutableSet<Term> res = DefaultImmutableSet.<Term> nil();
        FlatQuantifiedFormula flat = FormulaFlattener.flatten(formula,
                services);
        variables = flat.getVars();
        System.out.println("Flat Body: " + flat.getFlattenedBody().toString());
        System.out.println("Constraints: " + flat.getConstraints());
        HashSet<Term> falsifyca = falsify(flat.getFlattenedBody(), true);
        System.out.println("Falsify: " + falsifyca);
        HashSet<Term> matchca = new HashSet<Term>();
        for (Term term : flat.getConstraints()) {
            matchca.addAll(match(term));
        }
        System.out.println("Match: " + matchca.toString());
        return res;

    }

    private void addToClosure(HashSet<HashSet<Term>> equivB, Term term) {
        for (HashSet<Term> equivClass : equivB) {
        }

    }

    private boolean closureContains(HashSet<HashSet<Term>> equivB, Term term) {
        return false;
    }

    private HashSet<Term> getGroundTerms(Term term) {

        HashSet<Term> ret = new HashSet<Term>();
        if (isGround(term.sub(0)))
            ret.add(term.sub(0));
        if (isGround(term.sub(1)))
            ret.add(term.sub(1));
        return ret;
    }
}
