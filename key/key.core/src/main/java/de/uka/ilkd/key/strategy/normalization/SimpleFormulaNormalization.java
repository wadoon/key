package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.LinkedHashMap;
import org.key_project.util.collection.ImmutableArray;

import java.util.HashMap;
import java.util.LinkedHashSet;

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

    public static void enable() {enabled = true;}

    public static void disable() {enabled = false;}

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
    public SimpleFormulaNormalization(Node node, TermBuilder termBuilder, TermFactory termFactory,
                                      boolean skolemizeEX,
                                      boolean renameFirst) {
        this.node = node;
        this.termBuilder = termBuilder;
        this.termFactory = termFactory;
        this.skolemizeEx = skolemizeEX;
        this.renameFirst = renameFirst;
    }

    public SimpleFormulaNormalization(TermBuilder termBuilder, TermFactory termFactory,
                                      boolean skolemizeEX,
                                      boolean renameFirst) {
        this(null, termBuilder, termFactory, skolemizeEX, renameFirst);
    }

    private static Term lastFormula;
    private static Term lastResult;
    private static Object _LOCK = new Object();

    public Term getNormalized(Term formula) {
        if(!enabled) return formula;
        synchronized (_LOCK) {
            if(lastFormula == formula)  {
                if(node != null) {
                    node.getNodeInfo().incNormCall();
                }
                return lastResult;
            }
        }
        long ts = System.currentTimeMillis();
        Term result = normalize(formula).toTerm(termBuilder);
        ts = System.currentTimeMillis() - ts;

        synchronized (_LOCK) {
            if(node != null) {
                node.getNodeInfo().incNormCall();
                node.getNodeInfo().incNormExec();
                node.getNodeInfo().addNormTime(ts);
            }
            lastFormula = formula;
            lastResult = result;
        }
        return result;
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
        term = termFactory.createTerm(term.op(), new ImmutableArray<>(subs),
                term.boundVars(), term.javaBlock(), term.getLabels());

        return term;
    }

    private static final String SKOLEM_NAME_PREFIX = "skolem_fun_";
    private int skolem_counter = 0;

    private Term freshSkolemFun(Sort sort, Term[] subs) {
        //throw new RuntimeException("Creating a skolem function. this should never happen");
        Sort[] sorts = new Sort[subs.length];
        for(int i = 0; i < subs.length; i++) {
            sorts[i] = subs[i].sort();
        }
        return termBuilder.func(new Function(new Name(SKOLEM_NAME_PREFIX + skolem_counter++), sort, sorts), subs);
    }

    private QuantifiedClauseSet normalize(Term term) {
        return normalize(term, true, new HashMap<>(), new LinkedHashSet<>(), !renameFirst);
    }

    private QuantifiedClauseSet normalize(Term term, boolean polarity,
                                         HashMap<Term, Term> replaceMap, LinkedHashSet<Term> boundVars, boolean first) {
        int subs = term.subs().size();
        Operator op = term.op();

        if(subs == 1) {
            /*
             * UNARY f(a)
             */
            Term a = term.sub(0);

            if (op == Junctor.NOT) {
                // n(!a, p) --> n(a, !p)
                return normalize(a, !polarity, replaceMap, boundVars, first);
            }

            /*
             * Handling of quantifiers:
             *
             * ALL:
             *
             *  firstQV:
             *
             *      FORALL S x; P(...) ~> return QCS(FORALL x, normalized(P(...))
             *
             *  else:
             *
             *      FORALL S x; P(...) ~> return QCS(FORALL fresh_x, normalized(P(...))
             *
             * EX:
             */
            if (op instanceof Quantifier) {
                // get quantifier
                Quantifier quantifier = (Quantifier) op;
                // swap if polarity if negative
                if(!polarity) quantifier = invert(quantifier);
                // get quantifiable variable
                QuantifiableVariable qv = term.varsBoundHere(0).get(0);
                // create extended replace map
                HashMap<Term, Term> extReplaceMap = new HashMap<>(replaceMap);

                // skolemize existential quantifier if enabled
                if(skolemizeEx && (quantifier == Quantifier.EX)) {
                    // for E S x; add replacement x ~> skolem(<bound vars>)
                    extReplaceMap.put(termBuilder.var(qv), freshSkolemFun(qv.sort(), boundVars.toArray(new Term[0])));
                    return normalize(a, polarity, extReplaceMap, boundVars, first);
                }

                // initialize a freshQV as fresh variable if it is not first
                QuantifiableVariable freshQV = first ? qv : freshQV(qv);

                // create extended bound vars and add quantified variable
                LinkedHashSet<Term> extBoundVars = new LinkedHashSet<>(boundVars);
                extBoundVars.add(termBuilder.var(freshQV));

                // add replace(qv, freshQV) to extended replace map
                extReplaceMap.put(termBuilder.var(qv), termBuilder.var(freshQV));
                return new QuantifiedClauseSet(quantifier, freshQV, normalize(a, polarity,
                        extReplaceMap, extBoundVars, false));
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
                    return normalize(a, true, replaceMap, boundVars, first)
                            .or(normalize(b, false, replaceMap, boundVars, first))
                            .and(normalize(a, false, replaceMap, boundVars, first)
                                    .or(normalize(b, true, replaceMap, boundVars, first)));
                }
                else {
                    // !(a <-> b) --> (a & !b) | (!a & b)
                    return normalize(a, true, replaceMap, boundVars, first)
                            .and(normalize(b, false, replaceMap, boundVars, first))
                            .or(normalize(a, false, replaceMap, boundVars, first).and(
                                    normalize(b, true, replaceMap, boundVars, first)));
                }
            }

            if (op == Junctor.IMP) {
                if (polarity) {
                    // a->b --> !a | b
                    return normalize(a, false, replaceMap, boundVars, first)
                            .or(normalize(b, true, replaceMap, boundVars, first));
                }
                else {
                    // !(a->b) --> (a & !b)
                    return normalize(a, true, replaceMap, boundVars, first)
                            .and(normalize(b, false, replaceMap, boundVars, first));
                }
            }

            if (op == Junctor.AND) {
                if (polarity) {
                    // a & b is fine
                    return normalize(a, true, replaceMap, boundVars, first)
                            .and(normalize(b, true, replaceMap, boundVars, first));
                }
                else {
                    // !(a & b) --> !a | !b
                    return normalize(a, false, replaceMap, boundVars, first)
                            .or(normalize(b, false, replaceMap, boundVars, first));
                }
            }

            if (op == Junctor.OR) {
                if (polarity) {
                    // a | b is fine
                    return normalize(a, true, replaceMap, boundVars, first)
                            .or(normalize(b, true, replaceMap, boundVars, first));
                }
                else {
                    // !(a | b) --> !a & !b
                    return normalize(a, false, replaceMap, boundVars, first)
                            .and(normalize(b, false, replaceMap, boundVars, first));
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
                    return normalize(a, false, replaceMap, boundVars, first)
                            .or(normalize(b, true, replaceMap, boundVars, first))
                            .and(normalize(a, true, replaceMap, boundVars, first)
                                    .or(normalize(c, true, replaceMap, boundVars, first)));
                }
                else {
                    // ! (a ? b : c) --> (!a | ! b) & (a | !c)
                    return normalize(a, false, replaceMap, boundVars, first)
                            .or(normalize(b, false, replaceMap, boundVars, first))
                            .and(normalize(a, true, replaceMap, boundVars, first).or(
                                    normalize(c, false, replaceMap, boundVars, first)));
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

    private static Quantifier invert(Quantifier quantifier) {
        if(quantifier == Quantifier.ALL) return Quantifier.EX;
        if(quantifier == Quantifier.EX) return Quantifier.ALL;
        throw new RuntimeException(
                "Cannot handle Quantifier" + quantifier.toString());
    }

    private static final String VAR_NAME_PREFIX = "norm_var_";
    private int var_counter = 0;
    private LinkedHashMap<QuantifiableVariable, QuantifiableVariable> variableLookupMap = new LinkedHashMap<>();

    public QuantifiableVariable lookup(QuantifiableVariable qv) {
        return variableLookupMap.get(qv);
    }

    private QuantifiableVariable freshQV(QuantifiableVariable qv) {
        QuantifiableVariable fresh = (new LogicVariable(
                new Name(VAR_NAME_PREFIX + var_counter++), qv.sort()));
        variableLookupMap.put(fresh, qv);
        return fresh;
    }
}
