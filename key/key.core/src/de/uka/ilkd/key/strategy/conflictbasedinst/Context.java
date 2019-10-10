package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.conflictbasedinst.normalization.Clause;
import de.uka.ilkd.key.strategy.conflictbasedinst.normalization.Literal;
import de.uka.ilkd.key.strategy.conflictbasedinst.normalization.QuantifiedClauseSet;
import de.uka.ilkd.key.strategy.conflictbasedinst.statistics.CbiStatistics;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class Context {

    private static boolean print = false;
    /** All literals that are assumed to be true */
    private LinkedHashSet<Literal> literals;
    private LinkedHashSet<Term> terms;

    private HashMap<Term, LinkedHashSet<Term>> eqMap;
    private HashMap<Term, LinkedHashSet<Term>> uneqMap;
    private HashMap<Operator, Term> funMap;

    private LinkedHashMap<Operator, FunctionIndex> funIndexMap;
    private LinkedHashMap<Operator, ExtendedFunctionIndex> extFunIndexMap;

    private TermBuilder tb;
    private Services services;

    public Context(LinkedHashSet<Literal> literals, LinkedHashSet<Term> terms,
            HashMap<Term, LinkedHashSet<Term>> eqMap,
            HashMap<Term, LinkedHashSet<Term>> uneqMap,
            HashMap<Operator, Term> funMap,
            LinkedHashMap<Operator, FunctionIndex> funIndexMap,
            LinkedHashMap<Operator, ExtendedFunctionIndex> extFunIndexMap,
            TermBuilder tb, Services services) {
        super();
        this.literals = literals;
        this.terms = terms;
        this.eqMap = eqMap;
        this.uneqMap = uneqMap;
        this.funMap = funMap;
        this.funIndexMap = funIndexMap;
        this.extFunIndexMap = extFunIndexMap;
        this.tb = tb;
        this.services = services;
    }

    public Context(LinkedHashSet<QuantifiedClauseSet> ante,
            LinkedHashSet<QuantifiedClauseSet> succ,
            QuantifiedClauseSet qf) throws ContextUnsatisfiableException {
        this.tb = CbiServices.getTermBuiler();
        this.services = CbiServices.getServices();
        this.literals = new LinkedHashSet<Literal>();
        this.terms = new LinkedHashSet<Term>();
        this.eqMap = new LinkedHashMap<Term, LinkedHashSet<Term>>();
        this.uneqMap = new LinkedHashMap<Term, LinkedHashSet<Term>>();
        this.funMap = new LinkedHashMap<Operator, Term>();
        this.funIndexMap = new LinkedHashMap<Operator, FunctionIndex>();
        this.extFunIndexMap = new LinkedHashMap<Operator, ExtendedFunctionIndex>();
        for(QuantifiedClauseSet qcs : ante) {
            addAnte(qcs);
        }
        for(QuantifiedClauseSet qcs : succ) {
            addSucc(qcs);
        }
        buildFunctionIndex(qf);
        buildExtendedFunctionIndex();
        print("Context created.\nEqMap: " + eqMap.toString() + "\nunEqMap: " + uneqMap.toString() + "\nfunIndexMap: " + funMap.toString() + "\nextFunIdx: " + extFunIndexMap + "\nlits: " + literals);
    }

    private void buildFunctionIndex(QuantifiedClauseSet qf) {
        for(Clause clause: qf.getClauseSet().getClauses()) {
            for(Literal lit : clause.getLiterals()) {
                Term term = lit.getTerm();
                buildFunctionIndex(term);
            }
        }
    }

    private void buildFunctionIndex(Term term) {
        if(TermHelper.isAtom(term)) {
            funIndexMap.computeIfAbsent(term.op(), fi -> new FunctionIndex(eqMap, funMap)).add(term);
        }
        term.subs().forEach(sub -> buildFunctionIndex(sub));
    }

    private void buildExtendedFunctionIndex() {
        for(Term term: terms) {
            extFunIndexMap.computeIfAbsent(term.op(), fi -> new ExtendedFunctionIndex(eqMap)).add(term);
        }
    }

    public boolean entailsGroundEquality(Term a, Term b) {
        FunctionIndex idx_a = funIndexMap.get(a.op());
        FunctionIndex idx_b = funIndexMap.get(b.op());
        if(idx_a == null || idx_b == null) return false;
        Term rep_a = idx_a.get(a);
        Term rep_b = idx_b.get(b);
        if(rep_a == null || rep_b == null) return false;
        LinkedHashSet<Term> eqClass = eqMap.get(rep_a);
        return eqClass.contains(rep_b);
    }

    private void addAnte(QuantifiedClauseSet qcv) throws ContextUnsatisfiableException {
        addClauseSet(qcv, true);
    }

    private void addSucc(QuantifiedClauseSet qcv) throws ContextUnsatisfiableException {
        addClauseSet(qcv, false);
    }

    private void addClauseSet(QuantifiedClauseSet qcs, boolean polarity) throws ContextUnsatisfiableException {
        if(!polarity) {
            qcs = qcs.invert();
        }
        for(Literal gLit: qcs.getGroundLiterals(tb)) {
            addLiteral(gLit);
        }
    }

    private void addLiteral(Literal lit) throws ContextUnsatisfiableException {
        //System.out.println("literal: " + lit);
        literals.add(lit);
        if(lit.getPolarity() == false) {
            addTerm(lit.toTerm(tb));
        }
        Term term = lit.getTerm();
        addTerm(term);

        Operator op = term.op();
        if(op == Equality.EQUALS) {
            if(lit.getPolarity()) {
                addEquality(term.sub(0), term.sub(1));
            }else {
                addUnequality(term.sub(0), term.sub(1));
            }
        }

    }

    private void addTerm(Term term) {
        terms.add(term);
        if(TermHelper.isAtom(term)) {
            funMap.computeIfAbsent(term.op(), t -> term);
        }
        term.subs().forEach(sub -> addTerm(sub));
    }

    void addEquality(Term a, Term b) throws ContextUnsatisfiableException {
        if(unequal(a, b)) {
            throw new ContextUnsatisfiableException();
        }
        LinkedHashSet<Term> eq_a = eqMap.computeIfAbsent(a, set -> new LinkedHashSet<Term>(Arrays.asList(a)));
        LinkedHashSet<Term> eq_b = eqMap.computeIfAbsent(b, set -> new LinkedHashSet<Term>(Arrays.asList(b)));
        eq_a.addAll(eq_b);
        for(Term x: eq_a) {
            for(Term y: eq_b) {
                if(x == y) continue;
                if(unequal(x, y)) {
                    throw new ContextUnsatisfiableException();
                }
            }
        }
        eq_a.forEach(term -> eqMap.put(term, eq_a));
    }

    private static final LinkedHashSet<Term> EMPTY = new LinkedHashSet<Term>();

    private boolean unequal(Term x, Term y) {
        return uneqMap.getOrDefault(x, EMPTY).contains(y);
    }

    private boolean equal(Term x, Term y) {
        return eqMap.getOrDefault(x, EMPTY).contains(y);
    }

    private void addUnequality(Term a, Term b) throws ContextUnsatisfiableException {
        if(equal(a,b)) {
            throw new ContextUnsatisfiableException();
        }
        LinkedHashSet<Term> ueq_a = uneqMap.computeIfAbsent(a, set -> new LinkedHashSet<Term>());
        LinkedHashSet<Term> ueq_b = uneqMap.computeIfAbsent(b, set -> new LinkedHashSet<Term>());
        ueq_a.add(b);
        ueq_b.add(a);
    }

    private boolean closeable(Sequent seq) {
        if (services.getProof().name().toString().startsWith("CBI_SUBPROOF")) {
            return false;
        }
        CbiStatistics.startCbiSubproof();
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
        CbiStatistics.finishCbiSubproof();
        return ret;
    }

    private static final long timeoutInMillis = 100;
    private static final int maxRuleApps = 100;

    protected StrategyProperties setupStrategy() {
        final StrategyProperties sp = new StrategyProperties();
        sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
        sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_NONE);
        sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_NONE);
        sp.setProperty(StrategyProperties.MPS_OPTIONS_KEY, StrategyProperties.MPS_NONE);
        sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
        sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_OFF);
        sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_NONE);
        sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NONE);
        sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_OFF);
        sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF);
        sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_OFF);
        sp.setProperty(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY, StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER);
        sp.setProperty(StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY, StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OFF);
        return sp;
    }

    public LinkedHashSet<Term> getMatchingLiterals(Term constraint) {
        ExtendedFunctionIndex efi = extFunIndexMap.get(constraint.op());
        if(efi == null) return new LinkedHashSet<Term>();
        return new LinkedHashSet<Term>(efi.getTerms());
    }

    public HashMap<Term, LinkedHashSet<Term>> getEqualityClassMap() {
        return eqMap;
    }

    public HashMap<Term, LinkedHashSet<Term>> getUnequalityMap() {
        return uneqMap;
    }

    public Term arbitrary(Term grnd) {
        if(grnd == null) return null;
        for(Literal lit: literals) {
            Term term = lit.getTerm();
            if(grnd.sort() == term.sort()) return term;
        }
        return null;
    }

    private void print(Object o) {
        if(print) System.out.print(o);
    }

    private void println(Object o) {
        if(print) System.out.println(o);
    }

    public boolean entails(Term term) {
        if(term.op() == Junctor.NOT) {
            return !entails(term.sub(0));
        }else if (term.op() == Junctor.AND) {
            return entails(term.sub(0)) && entails(term.sub(1));
        }else if (term.op() == Junctor.OR) {
            return entails(term.sub(0)) || entails(term.sub(1));
        }else if (term.op() == Equality.EQUALS) {
            return equal(term.sub(0), term.sub(1)) || entailsGroundEquality(term.sub(0), term.sub(1));
        }else {
            return literals.contains(Literal.fromTerm(term));
        }
    }

    public boolean entails(LinkedHashSet<Term> subst) {
        for(Term term: subst) {
            if(!entails(term)) return false;
        }
        return true;
    }

    public Context copy() {
        LinkedHashSet<Literal> literals = new LinkedHashSet<Literal>(this.literals);
        LinkedHashSet<Term> terms = new LinkedHashSet<Term>(this.terms);

        HashMap<Term, LinkedHashSet<Term>> eqMap = new HashMap<Term, LinkedHashSet<Term>>();
        this.eqMap.entrySet().forEach(entry -> {
            LinkedHashSet<Term> eqs = new LinkedHashSet<Term>(entry.getValue());
            eqMap.put(entry.getKey(), eqs);
        });
        HashMap<Term, LinkedHashSet<Term>> uneqMap = new HashMap<Term, LinkedHashSet<Term>>();
        this.uneqMap.forEach((key, value) -> {
            uneqMap.put(key, new LinkedHashSet<Term>(value));
        });
        HashMap<Operator, Term> funMap = new HashMap<Operator, Term>();
        this.funMap.forEach((key,value) -> {
            funMap.put(key,value);
        });

        LinkedHashMap<Operator, FunctionIndex> funIndexMap = new LinkedHashMap<Operator, FunctionIndex>();
        this.funIndexMap.forEach((key, value) -> {
            funIndexMap.put(key, value.copy(eqMap, funMap));
        });
        LinkedHashMap<Operator, ExtendedFunctionIndex> extFunIndexMap = new LinkedHashMap<Operator, ExtendedFunctionIndex>();
        this.extFunIndexMap.forEach((key, value) -> {
            extFunIndexMap.put(key, value.copy(eqMap));
        });

        return new Context(literals, terms, eqMap, uneqMap, funMap, funIndexMap, extFunIndexMap, tb, services);

    }

    public void addEquality(Term constraint) throws ContextUnsatisfiableException {
        boolean p = true;
        if(constraint.op() == Junctor.NOT) {
            p = false;
            constraint = constraint.sub(0);
        }
        assert(constraint.op() == Equality.EQUALS): "can only add equalities";
        if(p) {
            addEquality(constraint.sub(0), constraint.sub(1));
        }else {
            addUnequality(constraint.sub(0), constraint.sub(1));
        }
    }
}
