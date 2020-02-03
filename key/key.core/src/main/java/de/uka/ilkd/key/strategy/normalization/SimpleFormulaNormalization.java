package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import org.jetbrains.annotations.NotNull;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

public class SimpleFormulaNormalization {

    private final TermBuilder termBuilder;
    private final TermFactory termFactory;

    private SimpleFormulaNormalization(TermBuilder termBuilder, TermFactory termFactory) {
        this.termBuilder = termBuilder;
        this.termFactory = termFactory;
    }

    public Term skolemize(Term formula) {
        QuantifiedClauseSet normalized = normalize(formula, true, new HashMap<Term, Term>(), new LinkedHashSet<Term>());
        LinkedHashSet<Term> boundVars = new LinkedHashSet<Term>();
        LinkedHashMap<Term, Term> replaceMap = new LinkedHashMap<Term, Term>();
        ImmutableList<QuantifiedTerm> quantifiers = DefaultImmutableSet.<QuantifiedTerm>nil().toImmutableList();
        for(QuantifiedTerm qt: normalized.getQuantifiedTerms()) {
            Term qv = termBuilder.var(qt.getQuantifiedVariable());
            if (qt.getQuantifier() == Quantifier.ALL) {
                boundVars.add(qv);
                quantifiers = quantifiers.append(qt);
            } else {
                replaceMap.put(qv, freshSkolemFun(qt.getQuantifiedVariable().sort(), boundVars.toArray(new Term[0])));
            }
        }
        LinkedHashSet<Clause> clauses = new LinkedHashSet<Clause>();
        for(Clause clause: normalized.getClauseSet().getClauses()) {
            LinkedHashSet<Literal> literals = new LinkedHashSet<Literal>();
            for(Literal lit: clause.getLiterals()) {
                literals.add(new Literal(replace(lit.getAtom(), replaceMap), lit.isPositive()));
            }
            clauses.add(new Clause(DefaultImmutableSet.fromSet(literals)));
        }
        QuantifiedClauseSet ret = new QuantifiedClauseSet(quantifiers,
                new ClauseSet(DefaultImmutableSet.fromSet(clauses)));
        return ret.toTerm(termBuilder);
    }

    private Term replace(Term term, @NotNull HashMap<Term, Term> replaceMap) {
        if (replaceMap.containsKey(term)) {
            term = replaceMap.get(term);
        }
        if (term.arity() == 0)
            return term;
        Term[] subs = new Term[term.arity()];
        for (int i = 0; i < term.subs().size(); i++) {
            subs[i] = replace(term.sub(i), replaceMap);
        }
        term = termFactory.createTerm(term.op(), new ImmutableArray<Term>(subs),
                term.boundVars(), term.javaBlock(), term.getLabels());

        return term;
    }

    private static final String SKOLEM_NAME_PREFIX = "skolem_fun_";
    private int skolem_counter = 0;

    private Term freshSkolemFun(Sort sort, Term[] subs) {
        Sort[] sorts = new Sort[subs.length];
        for(int i = 0; i < subs.length; i++) {
            sorts[i] = subs[i].sort();
        }
        return termBuilder.func(new Function(new Name(SKOLEM_NAME_PREFIX + skolem_counter++), sort, sorts), subs);
    }

    public QuantifiedClauseSet normalize(Term term, boolean polarity,
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
                extBoundVars.add(termBuilder.var(freshQV));
                extReplaceMap.put(termBuilder.var(qv), termBuilder.var(freshQV));
                return new QuantifiedClauseSet(polarity ? quant: invert(quant), freshQV, normalize(a, polarity,
                        extReplaceMap, extBoundVars));
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
        return new QuantifiedClauseSet(new Literal(replace(term, replaceMap), polarity));
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


}
