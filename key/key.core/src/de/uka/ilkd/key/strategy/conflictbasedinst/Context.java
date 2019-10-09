package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
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

    private QuantifiedClauseSet qf;
    /** A set of all unquantified clauses that are assumed to be true within the sequent **/
    private LinkedHashSet<Clause> clauses;
    private LinkedHashSet<Literal> literals;
    private LinkedHashSet<Term> terms;

    private HashMap<Term, LinkedHashSet<Term>> eqMap;
    private HashMap<Term, LinkedHashSet<Term>> uneqMap;
    private HashMap<Operator, Term> funMap;

    private LinkedHashMap<Operator, FunctionIndex> funIndexMap;
    private LinkedHashMap<Operator, ExtendedFunctionIndex> extFunIndexMap;

    private TermBuilder tb;
    private Services services;

    /** The antecedent for sub-proofs contains all unquantified clauses */
    private Semisequent cntx;

    public Context(LinkedHashSet<QuantifiedClauseSet> ante,
            LinkedHashSet<QuantifiedClauseSet> succ,
            QuantifiedClauseSet qf) {
        this.tb = CbiServices.getTermBuiler();
        this.services = CbiServices.getServices();
        this.qf = qf;
        this.clauses = new LinkedHashSet<Clause>();
        this.literals = new LinkedHashSet<Literal>();
        this.terms = new LinkedHashSet<Term>();
        this.eqMap = new LinkedHashMap<Term, LinkedHashSet<Term>>();
        this.uneqMap = new LinkedHashMap<Term, LinkedHashSet<Term>>();
        this.funMap = new LinkedHashMap<Operator, Term>();
        this.funIndexMap = new LinkedHashMap<Operator, FunctionIndex>();
        this.extFunIndexMap = new LinkedHashMap<Operator, ExtendedFunctionIndex>();
        ante.forEach(qcv -> addAnte(qcv));
        succ.forEach(qcv -> addSucc(qcv));
        buildFunctionIndex(qf);
        buildExtendedFunctionIndex();
        cntx = createCntx();
    }

    private Semisequent createCntx() {
        Semisequent cntx = Semisequent.EMPTY_SEMISEQUENT;
        Iterator<Clause> it = clauses.iterator();
        while(it.hasNext()) {
            Clause clause = it.next();
            if(clause.getLiterals().size() != 1) continue;
            Term term = clause.toTerm(tb);
            cntx = cntx.insertLast(new SequentFormula(term)).semisequent();
        }
        return cntx;
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
        funIndexMap.computeIfAbsent(term.op(), fi -> new FunctionIndex(eqMap, funMap)).add(term);
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

    private void addAnte(QuantifiedClauseSet qcv) {
        addClauseSet(qcv, true);
    }

    private void addSucc(QuantifiedClauseSet qcv) {
        addClauseSet(qcv, false);
    }

    private void addClauseSet(QuantifiedClauseSet qcs, boolean polarity) {
        if(qcs == qf) {
            return;
        }
        if(!polarity) {
            qcs = qcs.invert();
        }
        qcs.getUnquantifiedClauses(tb).forEach(clause -> {
                addClause(clause);
        });
    }

    private void addClause(Clause clause) {
        clauses.add(clause);
        for(Literal lit: clause.getLiterals()) {
            addLiteral(lit);
        }
    }

    private void addLiteral(Literal lit) {
        //System.out.println("literal: " + lit);
        literals.add(lit);
        Term term = lit.getTerm();
        boolean polarity = lit.getPolarity();
        addTerm(term);

        Operator op = term.op();
        if(op == Equality.EQUALS) {
            if(polarity) {
                addEquality(term.sub(0), term.sub(1));
            }else {
                addUnequality(term.sub(0), term.sub(1));
            }

        }else {
            funMap.putIfAbsent(op, term);
        }

    }

    private void addTerm(Term term) {
        terms.add(term);
        term.subs().forEach(sub -> addTerm(sub));
    }

    private void addEquality(Term a, Term b) {
        LinkedHashSet<Term> eq_a = eqMap.computeIfAbsent(a, set -> new LinkedHashSet<Term>(Arrays.asList(a)));
        LinkedHashSet<Term> eq_b = eqMap.computeIfAbsent(b, set -> new LinkedHashSet<Term>(Arrays.asList(b)));
        eq_a.addAll(eq_b);
        eq_a.forEach(term -> eqMap.put(term, eq_a));
    }

    private void addUnequality(Term a, Term b) {
        LinkedHashSet<Term> ueq_a = uneqMap.computeIfAbsent(a, set -> new LinkedHashSet<Term>());
        LinkedHashSet<Term> ueq_b = uneqMap.computeIfAbsent(b, set -> new LinkedHashSet<Term>());
        ueq_a.add(b);
        ueq_b.add(a);
    }

    public boolean equals(Term a, Term b) {
        LinkedHashSet<Term> eq_a = eqMap.get(a);
        if(eq_a == null) return false;
        return eq_a.contains(b);
    }

    public boolean unequals(Term a, Term b) {
        LinkedHashSet<Term> uneq_a = uneqMap.get(a);
        if(uneq_a == null) return false;
        return uneq_a.contains(b);
    }

    public boolean feasible(ConstrainedAssignment ca) {
        return feasible(tb.and(ca.getTerms()));
    }

    public boolean feasible(Term term) {
        return !entails(tb.not(term));
    }

    public boolean entails(Term term) {
        Sequent seq = Sequent.createSequent(cntx, new Semisequent(new SequentFormula(term)));
        boolean b =  closeable(seq);
        //System.out.println(literals + " entail " + seq + " : " + b);
        return b;
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

    public LinkedHashSet<Literal> getLiterals() {
        return literals;
    }

    public Semisequent getCntx() {
        return cntx;
    }
}
