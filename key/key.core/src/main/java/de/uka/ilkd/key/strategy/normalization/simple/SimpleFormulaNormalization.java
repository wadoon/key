package de.uka.ilkd.key.strategy.normalization.simple;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import org.key_project.util.collection.ImmutableArray;

import java.util.*;

public class SimpleFormulaNormalization {

    private final Node node;
    private final TermBuilder termBuilder;
    private final TermFactory termFactory;
    private final boolean skolemizeEx;
    private final boolean renameFirst;

    /*
    FormulaNormalization can by enabled and disabled system wide to allow controlling normalization by Proof Search
    Strategy.
     */
    private static boolean enabled = false;

    public static void enable() {
        enabled = true;
    }

    public static void disable() {
        enabled = false;
    }

    public static boolean isEnabled() {return enabled;}

    private static boolean simplify = false;

    public static void enableSimplify() {simplify = true;}

    public static void disableSimplify() {simplify = false;}

    public static boolean isSimplifying() {return simplify;}

    private static boolean miniscoping = false;

    public static void enableMiniscoping() {miniscoping = true;}

    public static void disableMiniscoping() {miniscoping = false;}

    public static boolean isMiniscoping() {return miniscoping;}

    /**
     * Creates a new simple formula normalization with the given term builder and factory.
     *
     * The normalization can normalize arbitrary formulas by calling {@link SimpleFormulaNormalization::}
     *
     * The formula normalization is further configured by deciding the handling of existential quantifiers and the
     * first quantified variable.
     *
     * If <code>skolemizeEX</code> is enabled existential quantified formulas <code>\exists S x: P(a, b, x, c)</code>
     * will be replaced by a fresh skolem function <code>SK_<n>(a, b, c)</n></code>, otherwise, the existential
     * quantified formula will be pulled left.
     *
     * If <code>renameFist</code> is enabled even the first quantified variable will be renamed, otherwise the first
     * quantified variable won't be replaced, to allow returning a valid result for instantiations of the AllLeft-Rule.
     * @param termBuilder the term builder to use
     * @param termFactory the term factory to use
     * @param skolemizeEX skolemize existential quantifiers
     * @param renameFirst rename first quantified variable
     */
    public SimpleFormulaNormalization(Goal goal,
                                      boolean skolemizeEx,
                                      boolean renameFirst) {
        this.node = goal.node();
        this.termBuilder = goal.proof().getServices().getTermBuilder();
        this.termFactory = goal.proof().getServices().getTermFactory();
        this.skolemizeEx = skolemizeEx;
        this.renameFirst = renameFirst;
    }

    private static Term lastFormula;
    private static Term lastNormalized;
    private static Term lastSimplified;
    private static Object _LOCK = new Object();

    private void traversePrint(Term formula, int depth) {
        System.out.println(tabs(depth) + formula.toString() + " " + formula.boundVars().toString() + " " + formula
        // .freeVars().toString()
        + System.lineSeparator() + tabs(depth) + boundVars(formula));
        if(formula.op() instanceof Quantifier) {
            Quantifier quant = (Quantifier) formula.op();
            checksubs(formula.sub(0), formula.varsBoundHere(0).get(0), depth);
        }
        formula.subs().forEach(term -> traversePrint(term, depth + 1));
    }

    private void checksubs(Term sub, QuantifiableVariable var, int depth) {
        System.out.println(sub.toString() + " " + sub.freeVars().toString() + " isbound? " + sub.freeVars().contains(var));
        sub.subs().forEach(term -> checksubs(term, var, depth));
    }

    private String boundVars(Term formula) {
        StringBuffer sb = new StringBuffer();
        sb.append("[");
        for(int i = 0; i < formula.subs().size(); i ++) {
            sb.append(formula.varsBoundHere(i));
            if(i != (formula.subs().size() -1)) sb.append(",");
        }
        sb.append("],[");
        formula.subs().forEach(term -> sb.append(boundVars(term) + ","));
        sb.append("]");
        return sb.toString();
    }

    private String tabs(int depth) {
        StringBuffer sb = new StringBuffer();
        for(int i = 0; i < depth; i++) sb.append("  ");
        return sb.toString();
    }

    public Term getNormalized(Term formula) {
        //traversePrint(formula, 0);
        if (!enabled) return formula;
        if (this.node != null) {
            this.node.getNodeInfo().incNormCall();
        }
        synchronized (_LOCK) {
            if (lastFormula == formula && lastNormalized != null) {
                return lastNormalized;
            }
        }
        long ts = System.nanoTime();
        Term smallclause;
        if(simplify) {
            SmallClauseNormalForm scnf = new SmallClauseNormalForm(termBuilder);
            smallclause = scnf.toSCNF(formula);
        }else {
            smallclause = formula;
        }
        Term result = norm(smallclause).toTerm(termBuilder);
        ts = System.nanoTime() - ts;


        synchronized (_LOCK) {
            if (node != null) {
                node.getNodeInfo().incNormExec();
                node.getNodeInfo().addNormTime(ts);
            }
            lastFormula = formula;
            lastNormalized = result;
            lastSimplified = null;
        }
        //System.out.println("Normalized: " + formula.toString() + "\tto: : " + result.toString());
        return result;
    }

    private Term substitute(Term term, Map<Term, Term> subst) {
        if (subst.containsKey(term)) {
            term = subst.get(term);
        }
        if (term.arity() == 0)
            return term;
        Term[] subs = new Term[term.arity()];
        for (int i = 0; i < term.subs().size(); i++) {
            subs[i] = substitute(term.sub(i), subst);
        }
        term = termFactory.createTerm(term.op(), new ImmutableArray<>(subs),
                term.boundVars(), term.javaBlock(), term.getLabels());

        return term;
    }

    private static final String SKOLEM_NAME_PREFIX = "skolem_fun_";
    private int skolem_counter = 0;

    private Term freshSkolemFun(Sort sort, Map<Term, Term> subst) {
        //throw new RuntimeException("Creating a skolem function. this should never happen");
        Term[] args = new Term[subst.size()];
        args = subst.values().toArray(args);
        Sort[] sorts = new Sort[subst.values().size()];
        for(int i = 0; i < args.length; i++) {
            sorts[i] = args[i].sort();
        }
        return termBuilder.func(new Function(new Name(SKOLEM_NAME_PREFIX + skolem_counter++), sort, sorts), args);
    }

    private ClauseSet skolemise(QuantifiedClauseSet qcs) {
        HashSet<Clause> clauses = new HashSet<>();
        for(Clause clause : qcs.getClauseSet().getClauses()) {
            HashSet<Literal> literals = new HashSet<>();
            for(Literal lit : clause.getLiterals()) {
                literals.add(new Literal(substitute(lit.getAtom(), qcs.getSkolemMap()), lit.getPolarity()));
            }
            clauses.add(new Clause(literals));
        }
        return new ClauseSet(clauses);
    }

    private QuantifiedClauseSet norm(Term term) {
        return norm(term, true, new HashMap<>());
    }

    private QuantifiedClauseSet normQuant(Quantifier quant, QuantifiableVariable qv, Term term, boolean polarity,
                                          Map<Term, Term> subst) {
        Map<Term, Term> nextSubst = new HashMap<Term, Term>(subst);
        if(!polarity) quant = invert(quant);
        Map<Term, Term> extSupst = new HashMap<>(subst);
        QuantifiableVariable freshQV = subst.isEmpty() ? qv : freshQV(qv.sort());
        if(polarity && quant == Quantifier.ALL || !polarity && quant == Quantifier.EX) {
            extSupst.put(termBuilder.var(qv), termBuilder.var(freshQV));
            return QuantifiedClauseSet.all(freshQV, norm(term, polarity, extSupst));
        }else {
            Term qvTerm = termBuilder.var(qv);
            Term skFun = freshSkolemFun(qv.sort(), subst);
            return QuantifiedClauseSet.exists(freshQV,qvTerm, skFun, norm(term, polarity, extSupst));
        }
    }

    private QuantifiedClauseSet normEqv(Term a, Term b, boolean polarity, Map<Term, Term> subst) {
        if(polarity) {
            return norm(a, false, subst).or(norm(b, true, subst))
                    .and(norm(a, true, subst).or(norm(b, false, subst)));
        }else {
            return norm(a, true, subst).and(norm(b, false, subst))
                    .or(norm(a, false, subst).and(norm(b, true, subst)));
        }
    }

    private QuantifiedClauseSet normImp(Term a, Term b, boolean polarity, Map<Term, Term> subst) {
        if(polarity) {
            return norm(a, false, subst).or(norm(b, true, subst));
        }else {
            return norm(a, true, subst).or(norm(b, false, subst));
        }
    }

    private QuantifiedClauseSet normAnd(Term a, Term b, boolean polarity, Map<Term, Term> subst) {
        if(polarity) {
            return norm(a, true, subst).and(norm(b, true, subst));
        }else {
            return norm(a, false, subst).or(norm(b, false, subst));
        }
    }

    private QuantifiedClauseSet normOr(Term a, Term b, boolean polarity, Map<Term, Term> subst) {
        if(polarity) {
            return norm(a, true, subst).or(norm(b, true, subst));
        }else {
            return norm(a, false, subst).and(norm(b, false, subst));
        }
    }

    private QuantifiedClauseSet normIfThenElse(Term a, Term b, Term c, boolean polarity, Map<Term, Term> subst) {
        if(polarity) {
            return norm(a, false, subst).or(norm(b, true, subst))
                    .and(norm(a, true, subst).or(norm(c, true, subst)));
        }else {
            return norm(a, true, subst).or(norm(b, false, subst))
                    .and(norm(a, false, subst).or(norm(c, false, subst)));
        }
    }


    private QuantifiedClauseSet norm(Term term, boolean polarity, Map<Term, Term> subst) {
        Operator op = term.op();
        if(op == Junctor.NOT)
            return norm(term.sub(0), !polarity, subst);
        if(op instanceof Quantifier)
            return normQuant((Quantifier) op, term.varsBoundHere(0).get(0), term.sub(0), polarity, subst);
        if (op == Equality.EQV)
            return normEqv(term.sub(0), term.sub(1), polarity, subst);
        if(op == Junctor.IMP)
            return normImp(term.sub(0), term.sub(1), polarity, subst);
        if(op == Junctor.AND)
            return normAnd(term.sub(0), term.sub(1), polarity, subst);
        if(op == Junctor.OR)
            return normOr(term.sub(0), term.sub(1), polarity, subst);
        if(op instanceof IfThenElse)
            return normIfThenElse(term.sub(0), term.sub(1), term.sub(2), polarity, subst);
        return new QuantifiedClauseSet(new Literal(substitute(term, subst), polarity));
    }

    private static Quantifier invert(Quantifier quantifier) {
        if(quantifier == Quantifier.ALL) return Quantifier.EX;
        if(quantifier == Quantifier.EX) return Quantifier.ALL;
        throw new RuntimeException(
                "Cannot handle Quantifier" + quantifier.toString());
    }

    private static final String VAR_NAME_PREFIX = "norm_var_";
    private int var_counter = 0;

    private QuantifiableVariable freshQV(Sort sort) {
        QuantifiableVariable fresh = (new LogicVariable(
                new Name(VAR_NAME_PREFIX + var_counter++), sort));
        return fresh;
    }
}
