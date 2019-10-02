package de.uka.ilkd.key.strategy.conflictbasedinst.normalization;

import java.util.HashMap;
import java.util.LinkedHashSet;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
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
import de.uka.ilkd.key.strategy.conflictbasedinst.TermHelper;

public class FormulaNormalization {

    private boolean skolemize = false;

    private TermBuilder tb;
    private TermFactory tf;


    private FormulaNormalization(boolean skolemize, Services services) {
        this.skolemize = skolemize;
        this.tb = services.getTermBuilder();
        this.tf = services.getTermFactory();
    }

    public static QuantifiedClauseSet normalizeToQuantifiedClauseSet(Term formula, boolean skolemize, Services services) {
        FormulaNormalization fn = new FormulaNormalization(skolemize, services);
        return fn.normalize(formula, true, new HashMap<Term, Term>(), new LinkedHashSet<Term>());
    }

    public static Term normalizeToTerm(Term formula, boolean skolemize, Services services) {
        //System.out.println("normalizing: " + LogicPrinter.quickPrintTerm(formula, services));
        long timer = System.nanoTime();
        Term term = normalizeToQuantifiedClauseSet(formula, skolemize, services).toTerm(services.getTermBuilder());
        timer = System.nanoTime() - timer;
        //System.out.println("normalized:  " + LogicPrinter.quickPrintTerm(term, services));
        return term;
    }



    private QuantifiedClauseSet normalize(Term term, boolean polarity,
            HashMap<Term, Term> replaceMap, LinkedHashSet<Term> boundVars) {

        /*
         * ZERO-ARITY
         *
         * A Literal can be returned as quantified clause set with zero
         * quantifiers and replaced Terms
         */
        if (isLit(term)) {
            System.out.println("Reached Literal: " + term.toString());
            return QuantifiedClauseSet
                    .create(Literal.fromTerm(replace(term, replaceMap)));
        }

        /*
         * UNARY f(a)
         */
        Operator op = term.op();
        Term a = term.sub(0);

        if (op == Junctor.NOT) {
            // n(!a, p) --> n(a, !p)
            return normalize(a, !polarity, replaceMap, boundVars);
        }

        // TODO rename variables on the fly
        if (op instanceof Quantifier) {
            QuantifiableVariable qv = term.varsBoundHere(0).get(0);
            HashMap<Term, Term> extReplaceMap = new HashMap<Term, Term>(
                    replaceMap);

            if (op == Quantifier.ALL && polarity
                    || op == Quantifier.EX && !polarity) {
                // all x : q --> all x : q
                // !exists x : q --> all x : !q
                LinkedHashSet<Term> extBoundVars = new LinkedHashSet<Term>(boundVars);
                QuantifiableVariable freshQV = freshQV(qv.sort());
                extBoundVars.add(tb.var(freshQV));
                extReplaceMap.put(tb.var(qv), tb.var(freshQV));
                return QuantifiedClauseSet.createAll(freshQV,
                        normalize(a, polarity, extReplaceMap, extBoundVars));
            }

            if (op == Quantifier.EX && polarity
                    || op == Quantifier.ALL && !polarity) {
                // ex x : q --> ex x : q
                // !all x : q --> ex x : !q
                if(skolemize) {
                    Term skolem = freshSkolemFun(qv.sort(), boundVars.toArray(new Term[0]));
                    extReplaceMap.put(tb.var(qv), skolem);
                    return normalize(a, polarity, extReplaceMap, boundVars);
                }else {
                    LinkedHashSet<Term> extBoundVars = new LinkedHashSet<Term>(boundVars);
                    QuantifiableVariable freshQV = freshQV(qv.sort());
                    extBoundVars.add(tb.var(freshQV));
                    extReplaceMap.put(tb.var(qv), tb.var(freshQV));
                    return QuantifiedClauseSet.createEx(freshQV,
                            normalize(a, polarity, extReplaceMap, extBoundVars));
                }
            }
        }

        /*
         * ARITY:2 f(a,b)
         */

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

        /*
         * ARITY:3 f(a,b,c)
         */

        Term c = term.sub(3);

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

        throw new RuntimeException(
                "Cannot handle Operator of Term:" + term.toString());
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
            return replaceMap.get(term);
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

    private ClauseSet distribute(Term term) {

        if (isLit(term)) {
            return ClauseSet.fromLiteral(Literal.fromTerm(term));
        }

        assert term.op() == Junctor.AND || term
                .op() == Junctor.OR : "Can only distribute conjunctions and disjunctions of literals";
        Operator op = term.op();
        ClauseSet a = distribute(term.sub(0));
        ClauseSet b = distribute(term.sub(1));

        if (op == Junctor.AND) {
            return a.and(b);
        }

        if (op == Junctor.OR) {
            return a.or(b);
        }

        throw new RuntimeException("Unknown Operator for distribution.");
    }

    private static boolean isLit(Term term) {
        return TermHelper.isLiteral(term) || term.op() == Junctor.TRUE
                || term.op() == Junctor.FALSE;
    }

}
