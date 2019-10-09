package de.uka.ilkd.key.strategy.conflictbasedinst.normalization;

import java.util.HashMap;
import java.util.LinkedHashSet;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.conflictbasedinst.TermHelper;
import de.uka.ilkd.key.strategy.conflictbasedinst.statistics.CbiStatistics;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Steps of normalization:
 *
 * quantified formula will be swapped to antec if ex in succ.
 * Normalized qf/seq is in form of quantified clause set
 * Skolemized qf/seq has skolemized existential quantifier
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public class FormulaNormalization {

    /** flag that determines if formula normalization is enabled for this proof **/
    private static boolean enabled;

    private TermBuilder tb;
    private TermFactory tf;

    private final Term qf;
    private Term normalizedQf;
    private Term skolemizedQf;
    private QuantifiedClauseSet normalizedQfClauseSet;
    private QuantifiedClauseSet skolemizedQfClauseSet;
    private final Sequent seq;
    private Sequent normalizedSeq;
    private LinkedHashSet<QuantifiedClauseSet> normalisedAnteClauseSets;
    private LinkedHashSet<QuantifiedClauseSet> normalisedSuccClauseSets;
    private Sequent skolemizedSeq;
    private LinkedHashSet<QuantifiedClauseSet> skolemizedAnteClauseSets;
    private LinkedHashSet<QuantifiedClauseSet> skolemizedSuccClauseSets;

    public static void setEnabled(boolean enabled) {
        FormulaNormalization.enabled = enabled;
    }

    public static boolean enabled() {
        return enabled;
    }

    private static Term lastQf;
    private static Sequent lastSeq;
    private static FormulaNormalization lastFormulaNormalization;

    public static FormulaNormalization create(Term qf, Sequent seq, Services services) {
        if(qf == lastQf && seq == lastSeq) {
            return lastFormulaNormalization;
        }
        return new FormulaNormalization(qf, seq, services);
    }

    public static FormulaNormalization create(RuleApp app, PosInOccurrence pos, Goal goal) {
        Term qf = pos.sequentFormula().formula();
        Sequent seq = goal.sequent();
        return create(qf, seq, goal.proof().getServices());
    }

    private FormulaNormalization(Term qf, Sequent seq, Services services) {
        this.qf = qf;
        this.seq = seq;
        this.tb = services.getTermBuilder();
        this.tf = services.getTermFactory();
    }

    public Term getNormalizedQf() {
        if(normalizedQf == null) normalizedQf = getNormalizedQfClauseSet().toTerm(tb);
        return normalizedQf;
    }

    public Term getSkolemizedQf() {
        if(skolemizedQf == null) skolemizedQf = getSkolemizedQfClauseSet().toTerm(tb);
        return skolemizedQf;
    }

    public QuantifiedClauseSet getNormalizedQfClauseSet() {
        if(normalizedQfClauseSet == null) {

            normalizedQfClauseSet = normalize(toAll(qf));
        }
        return normalizedQfClauseSet;
    }

    private Term toAll(Term term) {
        // assuming forall var: exp ==> ... and ... ==> exists var : exp
        assert(term.op() == Quantifier.EX || term.op() == Quantifier.ALL) : "Can only normalize if qf is quantified at top level";
        if(term.op() == Quantifier.EX) {
            return tb.all(term.boundVars().get(0), tb.not(term.sub(0)));
        }else {
            return term;
        }
    }

    public QuantifiedClauseSet getSkolemizedQfClauseSet() {
        if(skolemizedQfClauseSet == null) skolemizedQfClauseSet = skolemize(getNormalizedQfClauseSet());
        return skolemizedQfClauseSet;
    }

    public Sequent getSequent() {
        return seq;
    }

    public Term getQf() {
        return qf;
    }

    public Sequent getNormalizedSequent() {
        if(normalizedSeq == null) {
            Semisequent ante = Semisequent.EMPTY_SEMISEQUENT;
            Semisequent succ = Semisequent.EMPTY_SEMISEQUENT;
            for(QuantifiedClauseSet qcs: getNormalizedAnteClauseSets()) {
                ante = ante.insertLast(new SequentFormula(qcs.toTerm(tb))).semisequent();
            }
            for(QuantifiedClauseSet qcs: getNormalizedSuccClauseSets()) {
                succ = succ.insertLast(new SequentFormula(qcs.toTerm(tb))).semisequent();
            }
            normalizedSeq = Sequent.createSequent(ante, succ);
        }
        return normalizedSeq;
    }

    public LinkedHashSet<QuantifiedClauseSet> getNormalizedAnteClauseSets() {
        if(normalisedAnteClauseSets == null) {
            normalisedAnteClauseSets = new LinkedHashSet<QuantifiedClauseSet>();
            normalisedAnteClauseSets.add(getNormalizedQfClauseSet());
            normalizeSemisequent(normalisedAnteClauseSets, seq.antecedent());
        }
        return normalisedAnteClauseSets;
    }

    public LinkedHashSet<QuantifiedClauseSet> getNormalizedSuccClauseSets() {
        if(normalisedSuccClauseSets == null) {
            normalisedSuccClauseSets = new LinkedHashSet<QuantifiedClauseSet>();
            normalizeSemisequent(normalisedSuccClauseSets, seq.succedent());
        }
        return normalisedSuccClauseSets;
    }

    private void normalizeSemisequent(LinkedHashSet<QuantifiedClauseSet> clauseSet, Semisequent semiseq) {
        for(SequentFormula sf : semiseq.asList()) {
            // The quantified formula itself is added statically to the antecedent
            if(sf.formula() == qf) continue;
            clauseSet.add(normalize(sf.formula()));
        }
    }

    public LinkedHashSet<QuantifiedClauseSet> getSkolemizedAnteClauseSets() {
        if(skolemizedAnteClauseSets == null) {
            skolemizedAnteClauseSets = new LinkedHashSet<QuantifiedClauseSet>();
            skolemizedAnteClauseSets.add(getSkolemizedQfClauseSet());
            skolemizeSemisequent(skolemizedAnteClauseSets, getNormalizedAnteClauseSets());
        }
        return skolemizedAnteClauseSets;
    }

    public LinkedHashSet<QuantifiedClauseSet> getSkolemizedSuccClauseSets() {
        if(skolemizedSuccClauseSets == null) {
            skolemizedSuccClauseSets = new LinkedHashSet<QuantifiedClauseSet>();
            skolemizeSemisequent(skolemizedSuccClauseSets, getNormalizedSuccClauseSets());
        }
        return skolemizedSuccClauseSets;
    }

    public void skolemizeSemisequent(LinkedHashSet<QuantifiedClauseSet> skolemized, LinkedHashSet<QuantifiedClauseSet> normalized) {
        for(QuantifiedClauseSet qcs: normalized) {
            // The skolemized qf is added statically to the antecedent.
            if(qcs == normalizedQfClauseSet) continue;
            skolemized.add(skolemize(qcs));
        }
    }

    public Sequent getSkolemizedSequent() {
        if(skolemizedSeq == null) {
            Semisequent ante = Semisequent.EMPTY_SEMISEQUENT;
            Semisequent succ = Semisequent.EMPTY_SEMISEQUENT;
            for(QuantifiedClauseSet qcs: getSkolemizedAnteClauseSets()) {
                ante = ante.insertLast(new SequentFormula(qcs.toTerm(tb))).semisequent();
            }
            for(QuantifiedClauseSet qcs: getSkolemizedSuccClauseSets()) {
                succ = succ.insertLast(new SequentFormula(qcs.toTerm(tb))).semisequent();
            }
            skolemizedSeq = Sequent.createSequent(ante, succ);
        }
        return skolemizedSeq;
    }

    private QuantifiedClauseSet normalize(Term term) {
        CbiStatistics.startNormalization();
        QuantifiedClauseSet qcs = normalize(term, true, new HashMap<Term, Term>(), new LinkedHashSet<Term>());
        CbiStatistics.finishNormalization();
        return qcs;
    }

    private QuantifiedClauseSet skolemize(QuantifiedClauseSet qcs) {
        CbiStatistics.startNormalization();
        LinkedHashSet<Term> boundVars = new LinkedHashSet<Term>();
        LinkedHashMap<Term, Term> replaceMap = new LinkedHashMap<Term, Term>();
        ImmutableList<QuantifiedTerm> quantifiers = DefaultImmutableSet.<QuantifiedTerm> nil().toImmutableList();
        for(QuantifiedTerm qt: qcs.getQuantifiers()) {
            Term qv = tb.var(qt.getQv());
            if(qt.getQuantifier() == Quantifier.ALL) {
                boundVars.add(qv);
                quantifiers = quantifiers.append(qt);
            }else {
                replaceMap.put(qv, freshSkolemFun(qt.getQv().sort(), boundVars.toArray(new Term[0])));
            }
        }
        LinkedHashSet<Clause> clauses = new LinkedHashSet<Clause>();
        for(Clause clause: qcs.getClauseSet().getClauses()) {
            LinkedHashSet<Literal> literals = new LinkedHashSet<Literal>();
            for(Literal lit: clause.getLiterals()) {
                literals.add(Literal.fromTerm(replace(lit.getTerm(), replaceMap), lit.getPolarity()));
            }
            clauses.add(new Clause(DefaultImmutableSet.fromSet(literals)));
        }
        QuantifiedClauseSet ret = QuantifiedClauseSet.create(quantifiers, ClauseSet.create(DefaultImmutableSet.fromSet(clauses)));
        CbiStatistics.finishNormalization();
        return ret;
    }

    private QuantifiedClauseSet normalize(Term term, boolean polarity,
            HashMap<Term, Term> replaceMap, LinkedHashSet<Term> boundVars) {

        int subs = term.subs().size();
        Operator op = term.op();

        if(subs == 1) {
            /*
             * UNARY f(a)
             */
            Term a = term.sub(0);

            if (op == Junctor.NOT) {
                // n(!a, p) --> n(a, !p)
                return normalize(a, !polarity, replaceMap, boundVars);
            }

            if (op instanceof Quantifier) {
                Quantifier quant = (Quantifier) op;
                QuantifiableVariable qv = term.varsBoundHere(0).get(0);
                HashMap<Term, Term> extReplaceMap = new HashMap<Term, Term>(
                        replaceMap);
                LinkedHashSet<Term> extBoundVars = new LinkedHashSet<Term>(boundVars);
                QuantifiableVariable freshQV = freshQV(qv.sort());
                extBoundVars.add(tb.var(freshQV));
                extReplaceMap.put(tb.var(qv), tb.var(freshQV));
                return QuantifiedClauseSet.create(polarity ? quant: invert(quant), freshQV, normalize(a, polarity, extReplaceMap, extBoundVars));
            }
        }else if(subs == 2) {
            /*
             * ARITY:2 f(a,b)
             */
            Term a = term.sub(0);
            Term b = term.sub(1);

            if (op == Equality.EQV) {
                if (polarity) {
                    // a <-> b --> (a | !b) & (!a | b)
                    return normalize(a, true, replaceMap, boundVars)
                            .or(normalize(b, false, replaceMap, boundVars))
                            .and(normalize(a, false, replaceMap, boundVars)
                                    .or(normalize(b, true, replaceMap, boundVars)));
                }
                else {
                    // !(a <-> b) --> (a & !b) | (!a & b)
                    return normalize(a, true, replaceMap, boundVars)
                            .and(normalize(b, false, replaceMap, boundVars))
                            .or(normalize(a, false, replaceMap, boundVars).and(
                                    normalize(b, true, replaceMap, boundVars)));
                }
            }

            if (op == Junctor.IMP) {
                if (polarity) {
                    // a->b --> !a | b
                    return normalize(a, false, replaceMap, boundVars)
                            .or(normalize(b, true, replaceMap, boundVars));
                }
                else {
                    // !(a->b) --> (a & !b)
                    return normalize(a, true, replaceMap, boundVars)
                            .and(normalize(b, false, replaceMap, boundVars));
                }
            }

            if (op == Junctor.AND) {
                if (polarity) {
                    // a & b is fine
                    return normalize(a, true, replaceMap, boundVars)
                            .and(normalize(b, true, replaceMap, boundVars));
                }
                else {
                    // !(a & b) --> !a | !b
                    return normalize(a, false, replaceMap, boundVars)
                            .or(normalize(b, false, replaceMap, boundVars));
                }
            }

            if (op == Junctor.OR) {
                if (polarity) {
                    // a | b is fine
                    return normalize(a, true, replaceMap, boundVars)
                            .or(normalize(b, true, replaceMap, boundVars));
                }
                else {
                    // !(a | b) --> !a & !b
                    return normalize(a, false, replaceMap, boundVars)
                            .and(normalize(b, false, replaceMap, boundVars));
                }
            }
        }else if(subs == 3) {
            /*
             * ARITY:3 f(a,b,c)
             */
            Term a = term.sub(0);
            Term b = term.sub(1);
            Term c = term.sub(2);

            if (op instanceof IfThenElse) {
                if (polarity) {
                    // a ? b : c --> (!a | b) & (a | c)
                    return normalize(a, false, replaceMap, boundVars)
                            .or(normalize(b, true, replaceMap, boundVars))
                            .and(normalize(a, true, replaceMap, boundVars)
                                    .or(normalize(c, true, replaceMap, boundVars)));
                }
                else {
                    // ! (a ? b : c) --> (!a | ! b) & (a | !c)
                    return normalize(a, false, replaceMap, boundVars)
                            .or(normalize(b, false, replaceMap, boundVars))
                            .and(normalize(a, true, replaceMap, boundVars).or(
                                    normalize(c, false, replaceMap, boundVars)));
                }
            }
        }

        /*
         * Treat Everything else as Literal
         *
         * A Literal can be returned as quantified clause set with zero
         * quantifiers and replaced Terms
         */
        return QuantifiedClauseSet
                .create(Literal.fromTerm(replace(term, replaceMap), polarity));
    }

    private static Quantifier invert(Quantifier quant) {
        if(quant == Quantifier.ALL) return Quantifier.EX;
        if(quant == Quantifier.EX) return Quantifier.ALL;
        throw new RuntimeException(
                "Cannot handle Quantifier" + quant.toString());
    }

    private static final String VAR_NAME_PREFIX = "norm_var_";
    private int var_counter = 0;

    private QuantifiableVariable freshQV(Sort sort) {
        return (QuantifiableVariable) (new LogicVariable(
                new Name(VAR_NAME_PREFIX + var_counter++), sort));
    }

    private static final String SKOLEM_NAME_PREFIX = "skolem_fun_";
    private int skolem_counter = 0;

    private Term freshSkolemFun(Sort sort, Term[] subs) {
        Sort[] sorts = new Sort[subs.length];
        for(int i = 0; i < subs.length; i++) {
            sorts[i] = subs[i].sort();
        }
        return tb.func(new Function(new Name(SKOLEM_NAME_PREFIX + skolem_counter++), sort, sorts), subs);
    }

    private Term replace(Term term, HashMap<Term, Term> replaceMap) {
        if (replaceMap.containsKey(term)) {
            term = replaceMap.get(term);
        }
        if (term.arity() == 0)
            return term;
        Term[] subs = new Term[term.arity()];
        for (int i = 0; i < term.subs().size(); i++) {
            subs[i] = replace(term.sub(i), replaceMap);
        }
        term = tf.createTerm(term.op(), new ImmutableArray<Term>(subs),
                term.boundVars(), term.javaBlock(), term.getLabels());

        return term;
    }

    private static boolean isLit(Term term) {
        return TermHelper.isLiteral(term) || term.op() == Junctor.TRUE
                || term.op() == Junctor.FALSE;
    }

}
