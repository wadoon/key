package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class Context {

    private TermBuilder tb;
    private LinkedHashSet<Term> literals;
    private LinkedHashSet<Term> terms;
    private LinkedHashSet<Term> grounds;
    private HashMap<Operator, LinkedHashSet<Term>> functionMap;
    private HashMap<Term, LinkedHashSet<Term>> eqClassMap;
    private Services services;
    private Sequent cntx;

    protected Context(Term formula, Sequent sequent) {
        this.literals = new LinkedHashSet<Term>();
        this.terms = new LinkedHashSet<Term>();
        this.tb = CbiServices.getTermBuiler();
        this.functionMap = new LinkedHashMap<Operator, LinkedHashSet<Term>>();
        this.eqClassMap = new LinkedHashMap<Term, LinkedHashSet<Term>>();
        this.grounds = new LinkedHashSet<Term>();
        extractGroundLiterals(sequent.antecedent(), formula, true);
        extractGroundLiterals(sequent.succedent(), formula, false);
        this.services = CbiServices.getServices();
        sequent.antecedent().forEach(term -> grounds.add(term.formula()));
        sequent.succedent().forEach(term -> grounds.add(tb.not(term.formula())));
        SequentFormula sf = new SequentFormula(tb.and(grounds));
        cntx = Sequent.createAnteSequent(new Semisequent(sf));
    }

    private void extractGroundLiterals(Semisequent semiseq, Term formula,
            boolean polarity) {
        for (SequentFormula sf : semiseq) {
            // ignore quantified formula
            if (sf.formula() == formula)
                continue;
            extractGroundLiterals(sf.formula(), polarity);
        }
    }

    private void extractGroundLiterals(Term term, boolean polarity) {
        if (term.op() == Equality.EQUALS && TermHelper.isGround(term)) {
            addLiteral(term, polarity);
        }
        else if (term.op() == Junctor.NOT) {
            extractGroundLiterals(term.sub(0), !polarity);
        }
        else if (term.op() == Junctor.AND) {
            term.subs().forEach(sub -> extractGroundLiterals(sub, polarity));
        }
    }

    private void addLiteral(Term literal, boolean polarity) {
        literals.add(polarity ? literal : tb.not(literal));
        literal.subs().forEach(sub -> addAllTerm(sub));
        if(polarity) {
            addToEqClass(literal.sub(0), literal.sub(1));
        }
    }

    private void addToEqClass(Term a, Term b) {
        mergeEqClasses(a,b);
    }

    private LinkedHashSet<Term> getEqClass(Term term) {
        return eqClassMap.computeIfAbsent(term, eqClass -> new LinkedHashSet<Term>(Arrays.asList(term)));
    }

    private void mergeEqClasses(Term a, Term b) {
        LinkedHashSet<Term> eqClass = getEqClass(a);
        eqClass.addAll(getEqClass(b));
        eqClassMap.put(b, eqClass);
    }

    public LinkedHashSet<Term> getEqClassOf(Term term) {
        return eqClassMap.get(term);
    }

    private void addAllTerm(Term term) {
        addTerm(term);
        term.subs().forEach(sub -> addAllTerm(sub));
    }

    private void addTerm(Term term) {
        // terms that are not functions can be ignored as they are not
        // matched anyways
        //System.out.println("Evaluating: " + term.toString() + " op: " + term.op() + " opclass: " + term.op().getClass().getSimpleName());
        if (term.op() instanceof Function) {
            //System.out.println("Adding " + term.toString());
            terms.add(term);
            addToFunctionMap(term);
        }else {
            //System.out.println("not adding " + term.toString());
        }
    }

    private void addToFunctionMap(Term term) {
        functionMap.computeIfAbsent(term.op(), set -> new LinkedHashSet<Term>()).add(term);
    }

    public String toString() {
        String s = "Literals: ";
        s += literals.stream().map(term -> term.toString()).collect(Collectors.joining(", ", "{", "}"));
        s += " functions: ";
        s += functionMap.keySet().stream().map(op -> op.toString()).collect(Collectors.joining(", ", "{" , "}"));
        s += " eq classes: ";
        s += eqClassMap.toString();
        return s;
    }

    private static final long timeoutInMillis = Long.MAX_VALUE;
    private static final int maxRuleApps = Integer.MAX_VALUE;

    public boolean feasible(Term formula) {
        SequentFormula seqFormula = new SequentFormula(tb.and(tb.and(grounds), formula));
        Semisequent ante = new Semisequent(seqFormula);
        Sequent seq = Sequent.createAnteSequent(ante);
        return !closeable(seq);
    }

    public boolean feasible(Iterable<Term> terms) {
        SequentFormula seqFormula = new SequentFormula(tb.and(tb.and(grounds), tb.and(terms)));
        Semisequent ante = new Semisequent(seqFormula);
        Sequent seq = Sequent.createAnteSequent(ante);
        return !closeable(seq);
    }

    public boolean satisfies(Term formula) {
        return satisfies(new Term[] {formula});
    }

    public boolean satisfies(Term... terms) {
        Term formula = tb.and(terms);
        Semisequent antec = cntx.antecedent();
        Semisequent succ = new Semisequent(new SequentFormula(formula));
        Sequent seq = Sequent.createSequent(antec, succ);
        return closeable(seq);
    }

    public boolean closeable(Sequent seq) {
        if (services.getProof().name().toString().startsWith("CBI_SUBPROOF")) {
            return false;
        }
        CbiStatistics.pauseFeatureStopwatch();
        ProofEnvironment env = SideProofUtil
                .cloneProofEnvironmentWithOwnOneStepSimplifier(
                        services.getProof());
        ProofStarter ps = new ProofStarter(false);
        try {
            ps.init(seq, env, "CBI_SUBPROOF");
        }
        catch (ProofInputException e) {
            return false;
        }

        final StrategyProperties sp = setupStrategy();
        ps.setStrategyProperties(sp);
        ps.setMaxRuleApplications(maxRuleApps);
        ps.setTimeout(timeoutInMillis);
        final ApplyStrategyInfo info = ps.start();
        boolean ret = info.getProof().closed();
        CbiStatistics.resumeFeatureStopwatch();
        return ret;
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

    public boolean satisfies(Term funA, Term funB) {
        assert funA.op() instanceof Function && funB.op() instanceof Function : "Can only test satisfaction of eqality of functions";
        return false;
    }

    public LinkedHashSet<Term> getMatchingLiterals(Term constraint) {
        return functionMap.getOrDefault(constraint.op(), new LinkedHashSet<Term>());
    }

    public boolean sat(Iterable<Term> terms) {
        for(Term term: terms) {
            if(!sat(term)) return false;
        }
        return true;
    }

    private boolean sat(Term term) {
        for(Term ground: grounds) {
            if(!sat(ground, term)) return false;
        }
        return true;
    }

    private boolean sat(Term ground, Term term) {
        // TODO Auto-generated method stub
        return false;
    }
}
