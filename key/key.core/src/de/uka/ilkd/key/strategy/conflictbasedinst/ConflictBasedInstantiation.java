package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.strategy.conflictbasedinst.EquivalenceClosure.EquivalenceClass;
import de.uka.ilkd.key.strategy.conflictbasedinst.normalization.FormulaNormalization;
import de.uka.ilkd.key.strategy.conflictbasedinst.normalization.QuantifiedClauseSet;
import de.uka.ilkd.key.strategy.conflictbasedinst.statistics.CbiStatistics;

public class ConflictBasedInstantiation {

    private static final long FALSIFY_TIMEOUT = 100;
    private static final boolean print = false;
    private long falsify_start;

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


    private static boolean enabled = false;

    public static void setEnabled(boolean b) {
        enabled = b;
    }

    public static boolean enabled() {
        return enabled;
    }

    private static boolean inducing = false;

    public static void setInducing(boolean b) {
        inducing = b;
    }

    public static boolean inducing() {
        return inducing;
    }

    /**
     * The formula that was used in the last run, saved to return same result if
     * called on the same formula/sequent twice.
     */
    private Term lastFormula;
    /**
     * The sequent to build the context from.
     */
    private Sequent lastSequent;

    /**
     * The holder for CBIs TermBuilder
     */
    private TermBuilder tb;
    private TermFactory tf;

    /**
     * The context (may be stored between runs later)
     */
    private Context context;

    private LinkedHashSet<Term> variables;

    /**
     * The result of the last run.
     */
    private CbiResult result;

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
    public CbiResult findConflictingTerm(Term formula, Sequent sequent, Services services) {
        if (this.lastFormula == formula && this.lastSequent == sequent) {
            return result;
        }
        if(!enabled() || !TermHelper.containsEqualityInScope(formula)) {
            result = CbiResult.NONE;
        }
        println("Run CBI...");
        long start = System.currentTimeMillis();
        /*
         * Find conflicting term on fresh formula
         */
        this.lastFormula = formula;
        this.lastSequent = sequent;

        CbiStatistics.startCbi();
        // register current termbuilder
        this.tb = services.getTermBuilder();
        this.tf = services.getTermFactory();
        CbiServices.setTermBuiler(tb);
        CbiServices.setTermFactory(tf);
        CbiServices.setServices(services);

        print("normalize... ");
        FormulaNormalization fn = FormulaNormalization.create(formula, sequent, services);
        formula = fn.getSkolemizedQf();
        Term prepForm = fn.getSkolemizedQfClauseSet().getClauseSet().toTerm(tb);
        QuantifiedClauseSet formulaCl = fn.getSkolemizedQfClauseSet();
        LinkedHashSet<QuantifiedClauseSet> ante = fn.getSkolemizedAnteClauseSets();
        LinkedHashSet<QuantifiedClauseSet> succ = fn.getSkolemizedSuccClauseSets();
        println("finished");

        /*
         * Create context
         */
        this.context = new Context(ante, succ, formulaCl);
        print("create context... ");
        ContextSingleton.setContext(context);
        println("finished.");

        this.variables = new LinkedHashSet<Term>();
        variables.addAll(formulaCl.getQuantifiersAsTerms(tb));
        print("falsify... ");
        falsify_start = System.currentTimeMillis();
        LinkedHashSet<CbiPair> pairs = falsify(prepForm, true,
                new ConstrainedAssignment(),
                MatchingConstraints.extractFrom(prepForm));
        println("finished.");
        print("extract... ");
        result = extractConflictingSubstitution(pairs);
        CbiStatistics.finishCbi(result.getResult() != null, result.isInducing());
        println("finished.");
        println(result + " took: " + (System.currentTimeMillis() - start) + "ms");
        return result;
    }

    private CbiResult extractConflictingSubstitution(LinkedHashSet<CbiPair> pairs) {
        LinkedHashSet<CbiResult> inducing = new LinkedHashSet<CbiResult>();
        for(CbiPair pair: pairs) {
            ConstrainedAssignment ca = pair.getConstrainedAssignment();
            CbiResult result = null;
            if(context.feasible(ca)) {
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
                for (EquivalenceClass eqc : ec.getEquivalenceClasses()) {
                    Term subst = tb.and(c);
                    Term grnd = null;
                    if (eqc.containsGround()) {
                        grnd = eqc.getGroundTerm();
                    }else {
                        grnd = context.arbitrary(eqc.first());
                    }
                    if(grnd == null) {
                        continue;
                    }

                    for (Term term : eqc) {
                        if (!(term.equals(grnd))) {
                            //subst = tb.subst(qv, grnd, subst);
                            subst = TermHelper.replaceAll(term, grnd, subst);
                            if (variables.contains(term)) {
                                groundSubst.add(grnd);
                                if(variables.iterator().next().equals(term)) {
                                    result = new CbiResult(grnd, false);
                                    if (context.entails(subst)) {
                                        this.result = result;
                                        return result;
                                    }
                                    else {
                                        // println("found inducing: " +
                                        // result.toString());
                                        result.setInducing(true);
                                        inducing.add(result);
                                    }
                                }
                            }
                        }
                    }
                }
            }else {
                //println("Not feasible: " + ca);
            }
        }
        if(CbiServices.getInducing()) {
            Iterator<CbiResult> it = inducing.iterator();
            if(it.hasNext()) {
                result = it.next();
                return result;
            }
        }

        return new CbiResult(null, false);
    }

    private LinkedHashSet<CbiPair> falsify(Term formula, boolean polarity,
            ConstrainedAssignment ca, MatchingConstraints mc) {
        LinkedHashSet<CbiPair> result = new LinkedHashSet<CbiPair>();
        if((System.currentTimeMillis() - falsify_start) > FALSIFY_TIMEOUT) {
            return result;
        }
        if(!context.feasible(ca)) {
            return result;
        }
        if (TermHelper.isGround((formula))) {
            if (context.entails(polarity ? formula : tb.not(formula))) {
                result.add(new CbiPair(ca, mc));
            }
            return result;
        }
        else if (TermHelper.isEquality(formula)) {
            Term constraint = polarity ? TermHelper.negate(formula) : formula;
            return match(mc.only(formula.subs()),
                    ca.addConstraint(constraint),
                    mc.without(formula.subs()));
        }
        else if (TermHelper.isNegation(formula)) {
            result.addAll(falsify(formula.sub(0), !polarity, ca, mc));
            return result;
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
            return result;
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
            return result;
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
            return result;
        }
        return result;
    }

    private LinkedHashSet<CbiPair> match(MatchingConstraints mc,
            ConstrainedAssignment ca, MatchingConstraints rest) {
        //println("Match: \t" + mc.toString() + "\t" + ca.toString()
        //+ "\t" + rest.toString());
        LinkedHashSet<CbiPair> ret = new LinkedHashSet<CbiPair>();
        if((System.currentTimeMillis() - falsify_start) > FALSIFY_TIMEOUT) {
            return ret;
        }
        if(!context.feasible(ca)) {
            return ret;
        }
        if (mc.isEmpty()) {
            ret.add(new CbiPair(ca, mc));
        }
        else {
            Term constraint = mc.getFirst();
            LinkedHashSet<Term> matches = context.getMatchingLiterals(constraint);
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

    private void print(Object x) {
        if(print == false) return;
        System.out.print(x);
    }

    private void println(Object x) {
        if(print == false) return;
        System.out.println(x);
    }

}
