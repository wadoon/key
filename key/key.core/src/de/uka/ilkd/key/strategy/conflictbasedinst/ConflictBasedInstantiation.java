package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.strategy.conflictbasedinst.EquivalenceClosure.EquivalenceClass;

public class ConflictBasedInstantiation {

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
        private static final ConflictBasedInstantiation INSTANCE = new ConflictBasedInstantiation();
    }

    /**
     * Empty constructor for singleton creation.
     */
    private ConflictBasedInstantiation() {
    }

    /**
     * Returns this instantiation strategies singleton instance.
     *
     * @return This singletons instance
     */
    public static ConflictBasedInstantiation getInstance() {
        return Holder.INSTANCE;
    }

    /**
     * The formula that was used in the last run, saved to return same result if
     * called on the same formula/sequent twice.
     */
    private Term lastFormula;
    /**
     * The sequent to build the context from.
     */
    private Sequent sequent;

    /**
     * The holder for CBIs TermBuilder
     */
    private TermBuilder tb;
    private TermFactory tf;

    /**
     * The consecutive number for renamed quantified variables
     */
    private int qvNumber;

    private static final String CBI_QV_NAME = "cbi_renamed_qv_";

    /**
     * The consecutive number for skolem functions
     */
    private int skolemNumber;

    private static final String CBI_SKOLEM_FUNCTION_NAME = "cbi_scolem_function_";

    /**
     * The context (may be stored between runs later)
     */
    private Context context;

    /**
     * The result of the last run.
     */
    private Term result;

    private LinkedHashSet<Term> inducing;

    private LinkedHashSet<Term> variables;

    /**
     * Returns a term to substitute the formula with to create an instance of
     * the formula that leads to apply a closing rule on the sequent or
     * <code>null</code> if no such term can be found.
     *
     * This procedure allows to find instances for universally quantified
     * formulas of the sequents antecedent or existentially quantified formulas
     * of the sequents succedent. If the formula does not conform to this
     * requirement <code>null</code> is returned.
     *
     * The procedure returns terms so that the substituted instance of the
     * formula suffices to apply a close rule on the sequent. If conflict
     * inducing instances are enabled the procedure also returns terms to create
     * instances that lead to new constraints and thereby can be supportive to
     * close the sequent in a later run. Conflict inducing terms will be
     * returned only if no conflicting term can be found.
     *
     * @param formula
     * @param sequent
     * @param services
     * @return a conflicting or conflict inducing term to instantiate the
     *         formula or null if no term found.
     * @throws IllegalArgumentException
     *             if formula is not ALL in antecedent or EX in succedent.
     */
    public Term findConflictingTerm(Term formula, Sequent sequent,
            PosInOccurrence pos, Services services) {
        if (this.lastFormula == formula && this.sequent == sequent) {
            // TODO find next conflicting term
            /*
             * This can actually not happen as the sequent changes if one
             * instance was found To handle that build context from sequent
             * incrementally (traverse sequent for unknown terms) and keep state
             * if formula is the same (cbi called on same formula repeatedly)
             */
        }
        if(!TermHelper.containsEqualityInScope(formula)) {
            return null;
        }
        /*
         * Find conflicting term on fresh formula
         */
        this.lastFormula = formula;
        this.sequent = sequent;
        // register current termbuilder
        this.tb = services.getTermBuilder();
        this.tf = services.getTermFactory();
        CbiServices.setTermBuiler(tb);
        CbiServices.setTermFactory(tf);
        CbiServices.setServices(services);
        // reset consecutive numbers
        this.qvNumber = 0;
        this.skolemNumber = 0;
        this.variables = new LinkedHashSet<Term>();

        if (!((formula.op() == Quantifier.ALL && pos.isInAntec())
                || (formula.op() == Quantifier.EX && !pos.isInAntec()))) {
            throw new IllegalArgumentException(
                    "Can only handle ALL in antecedent or EX in succedent.");
        }

        /*
         * Handle EX in succedent ( A => \exists x:p(x), S --> A, \forall x;
         * !p(x) => S)
         */
        if (formula.op() == Quantifier.EX) {
            formula = tb.all(formula.boundVars(), tb.not(formula.sub(0)));
        }

        /*
         * Prepare formula
         */

        HashMap<Term, Term> replaceMap = new HashMap<Term, Term>();
        LinkedHashSet<Term> boundVars = new LinkedHashSet<Term>();
        Term prepForm = prepareFormula(
                formula, replaceMap, boundVars);

        /*
         * Create context
         */
        context = new Context(prepForm, sequent);
        ContextSingleton.setContext(context);

        LinkedHashSet<CbiPair> pairs = falsify(prepForm, true,
                new ConstrainedAssignment(),
                MatchingConstraints.extractFrom(prepForm));
        return extractConflictingSubstitution(pairs);
    }

    private Term prepareFormula(Term formula, HashMap<Term, Term> replaceMap, LinkedHashSet<Term> boundVars) {
        if(replaceMap.containsKey(formula)) {
            return replaceMap.get(formula);
        }
        LinkedHashSet<Term> extendedBoundVars = new LinkedHashSet<Term>(boundVars);
        HashMap<Term, Term> extendedReplaceMap = new HashMap<Term, Term>(replaceMap);
        if (formula.op() == Quantifier.ALL) {
            for(QuantifiableVariable qv: formula.boundVars()) {
                Term freshQV = createQuantVar(qv.sort());
                extendedReplaceMap.put(tb.var(qv), freshQV);
                extendedBoundVars.add(freshQV);
                variables.add(freshQV);
            }
            return prepareFormula(formula.sub(0), extendedReplaceMap, extendedBoundVars);
        }
        else if (formula.op() == Quantifier.EX) {
            Term[] bvArray = boundVars.toArray(new Term[0]);
            for(QuantifiableVariable qv: formula.boundVars()) {
                Term skolem = createSkolemFunction(qv.sort(), bvArray);
                extendedReplaceMap.put(tb.var(qv), skolem);
            }
            return prepareFormula(formula.sub(0), extendedReplaceMap, boundVars);
        }

        Term[] subs = new Term[formula.subs().size()];
        for (int i = 0; i < formula.subs().size(); i++) {
            subs[i] = prepareFormula(formula.subs().get(i), replaceMap, boundVars);
        }
        return tf.createTerm(formula.op(), new ImmutableArray<Term>(subs), formula.boundVars(), formula.javaBlock(), formula.getLabels());
    }

    private Term createQuantVar(Sort sort) {
        return TermHelper.quantVar(CBI_QV_NAME + ++qvNumber, sort);
    }

    private Term createSkolemFunction(Sort sort, Term[] subs) {
        Sort[] sorts = new Sort[subs.length];
        for(int i = 0; i < subs.length; i++) {
            sorts[i] = subs[i].sort();
        }
        return tb.func(new Function(new Name(CBI_SKOLEM_FUNCTION_NAME + ++skolemNumber), sort, sorts), subs);
    }

    private Term extractConflictingSubstitution(LinkedHashSet<CbiPair> pairs) {
        LinkedHashSet<Term> inducing = new LinkedHashSet<Term>();
        for(CbiPair pair: pairs) {
            ConstrainedAssignment ca = pair.getConstrainedAssignment();
            if(ca.isContextFeasible()) {
                LinkedHashSet<Term> b = new LinkedHashSet<Term>();
                LinkedHashSet<Term> c = new LinkedHashSet<Term>();
                EquivalenceClosure ec = new EquivalenceClosure();

                for (Term term : ca.getTerms()) {
                    if (ec.addEquality(term)) {
                        b.add(term);
                    }
                    else {
                        c.add(term);
                    }
                }

                LinkedHashSet<Term> groundSubst = new LinkedHashSet<Term>();
                Term subst = tb.and(c);
                for (EquivalenceClass eqc : ec.getEquivalenceClasses()) {
                    // System.out.println("Checking eqc: " + eqc.toString());
                    if (eqc.containsGround()) {
                        Term grnd = eqc.getGroundTerm();
                        // System.out.println("Ground Term: " + grnd.toString());
                        for (Term term : eqc) {
                            if (!(term.equals(grnd))) {
                                //subst = tb.subst(qv, grnd, subst);
                                subst = TermHelper.replaceAll(term, grnd, subst);
                                if (variables.contains(term)) {
                                    // System.out.println("Adding GroundSubst: " +
                                    // grnd.toString());
                                    groundSubst.add(grnd);
                                    if(variables.iterator().next().equals(term)) {
                                        result = grnd;
                                    }
                                }
                            }
                        }
                    }
                    else {
                        // System.out.println("Could not find ground subst.");
                        // TODO take arbitrary terms from context
                    }
                }

                // System.out.println("subst: " + subst.toString());
                if (context.satisfies(subst)) {
                    //System.out.println("found result: " + result);
                    return result;
                }
                else {
                    // System.out.println("found inducing: " + result.toString());
                    inducing.add(result);
                }
            }else {
                // System.out.println("Not feasible: " + ca.toString());
            }
        }
        if(CbiServices.getInducing()) {
            Iterator<Term> it = inducing.iterator();
            if(it.hasNext()) {
                result = it.next();
                return result;
            }
        }else {
            System.out.println("No Inducing today");
        }

        return null;
    }

    private LinkedHashSet<CbiPair> falsify(Term formula, boolean polarity,
            ConstrainedAssignment ca, MatchingConstraints mc) {
        // System.out.println("Calling falsify with: " + formula.toString() + ", "
        //        + polarity + ", " + ca.toString() + ", " + mc.toString());
        LinkedHashSet<CbiPair> result = new LinkedHashSet<CbiPair>();
        if (TermHelper.isGround((formula))) {
            if (context.satisfies(formula) != polarity) {
                result.add(new CbiPair(ca, mc));
            }
        }
        else if (TermHelper.isEquality(formula)) {
            return match(mc.only(formula.subs()),
                    ca.addConstraint(
                            polarity ? TermHelper.negate(formula) : formula),
                    mc.without(formula.subs()));
        }
        else if (TermHelper.isNegation(formula)) {
            falsify(formula.sub(0), !polarity, ca, mc);
        }
        else if (TermHelper.isOr(formula)) {
            if (polarity) {
                for (CbiPair pair : falsify(formula.sub(0), polarity, ca, mc)) {
                    result.addAll(falsify(formula.sub(1), polarity,
                            pair.getConstrainedAssignment(),
                            pair.getMatchingConstraints()));
                }
            }
            else {
                result.addAll(falsify(formula.sub(0), polarity, ca, mc));
                result.addAll(falsify(formula.sub(1), polarity, ca, mc));
            }
        }
        else if (TermHelper.isAnd(formula)) {
            // a & b = !(!a | !b)
            if (polarity) {
                result.addAll(falsify(formula.sub(0), !polarity, ca, mc));
                result.addAll(falsify(formula.sub(1), !polarity, ca, mc));
            }
            // !(a & b) = !a | !b
            else {
                for (CbiPair pair : falsify(formula.sub(0), !polarity, ca,
                        mc)) {
                    result.addAll(falsify(formula.sub(1), !polarity,
                            pair.getConstrainedAssignment(),
                            pair.getMatchingConstraints()));
                }
            }
        }
        else if (TermHelper.isImp(formula)) {
            // a -> b = !a | b
            if (polarity) {
                for (CbiPair pair : falsify(formula.sub(0), !polarity, ca,
                        mc)) {
                    result.addAll(falsify(formula.sub(1), polarity,
                            pair.getConstrainedAssignment(),
                            pair.getMatchingConstraints()));
                }
            }
            // !(a -> b) = !(!a | b) = a & !b
            else {
                result.addAll(falsify(formula.sub(0), !polarity, ca, mc));
                result.addAll(falsify(formula.sub(1), polarity, ca, mc));
            }
        }
        return result;
    }

    private LinkedHashSet<CbiPair> match(MatchingConstraints mc,
            ConstrainedAssignment ca, MatchingConstraints rest) {
        //System.out.println("Match: \t" + mc.toString() + "\t" + ca.toString()
        //+ "\t" + rest.toString());
        LinkedHashSet<CbiPair> ret = new LinkedHashSet<CbiPair>();
        if (mc.isEmpty()) {
            ret.add(new CbiPair(ca, mc));
        }
        else {
            Term constraint = mc.getFirst();
            LinkedHashSet<Term> matches = context
                    .getMatchingLiterals(constraint);
            //System.out.println("Matching Literals: " + matches.toString());
            MatchingConstraints newMc = mc.without(constraint)
                    .union(rest.only(constraint.subs()));
            MatchingConstraints newRest = rest.without(constraint.subs());
            for (Term match : matches) {
                ret.addAll(match(newMc, ca.addAssignment(constraint, match),
                        newRest));
            }
        }
        return ret;
    }

}
