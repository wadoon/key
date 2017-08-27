// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.util;

import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.UpdateApplication;

/**
 * Converter from formulas into conjunctive normal form, main method
 * {@link #convertToCNF(Term)}. The returned formulas are logically equivalent,
 * so no Skolemization takes place! Quantifiers will still be included.
 *
 * @author Dominic Steinhoefel
 */
public class CNFConverter {
    /**
     * The {@link Logger} for this class.
     */
    private static final Logger LOGGER = LogManager.getFormatterLogger();

    /**
     * The {@link TermBuilder} object.
     */
    private TermBuilder tb;

    /**
     * The {@link TermFactory} of {@link #tb}.
     */
    private TermFactory tf;

    /**
     * Constructor.
     *
     * @param tb
     *            The {@link TermBuilder} to use for constructing CNF formulas.
     */
    public CNFConverter(TermBuilder tb) {
        this.tb = tb;
        this.tf = tb.tf();
    }

    /**
     * Converts the {@link Term} t into CNF.
     *
     * @param t
     *            {@link Term} to convert.
     * @return A logically equivalent CNF of t.
     */
    public Term convertToCNF(Term t) {
        List<Term> updates = null;

        if (t.op() instanceof UpdateApplication) {
            updates = LogicUtilities.getUpdates(t);
        }

        final Term cnfMatrix = applyDistributivityLaws(
            splitQuantifiers(pushNegationsInvards(
                eliminateBiImplications(TermBuilder.goBelowUpdates(t)))));

        if (updates != null) {
            Term result = cnfMatrix;
            for (int i = updates.size() - 1; i >= 0; i--) {
                result = tb.apply(updates.get(i), result);
            }
            return result;
        } else {
            return cnfMatrix;
        }
    }

    /**
     * Replaces (bi)implications by the corresponding formulas with negations,
     * disjunctions and conjunctions only.
     *
     * @param t
     *            The {@link Term} of which to remove (bi)implications.
     * @return A logically equivalent {@link Term} without (bi)implications.
     */
    protected Term eliminateBiImplications(Term t) {
        if (t.op() == Junctor.IMP) {
            return tb.or(tb.not(eliminateBiImplications(t.sub(0))),
                eliminateBiImplications(t.sub(1)));
        } else if (t.op() == Equality.EQV) {
            return tb.and(
                tb.or(//
                    tb.not(eliminateBiImplications(t.sub(0))),
                    eliminateBiImplications(t.sub(1))),
                tb.or(//
                    tb.not(eliminateBiImplications(t.sub(1))),
                    eliminateBiImplications(t.sub(0))));
        } else {
            return recurse(t, t1 -> eliminateBiImplications(t1));
        }
    }

    /**
     * Converts a formula without (bi)implications into NNF by pushing negations
     * to the level of atoms.
     *
     * @param t
     *            {@link Term} to convert into NNF; must not include
     *            (bi)implications.
     * @return A logically equivalent {@link Term} in NNF.
     */
    protected Term pushNegationsInvards(Term t) {
        if (t.op() == Junctor.NOT) {
            final Term sub = t.sub(0);

            if (sub.op() == Quantifier.ALL) {
                final QuantifiableVariable qv = sub.boundVars().get(0);
                return tb.ex((QuantifiableVariable) qv,
                    pushNegationsInvards(tb.not(sub.sub(0))));
            } else if (sub.op() == Quantifier.EX) {
                final QuantifiableVariable qv = sub.boundVars().get(0);
                return tb.all(qv, pushNegationsInvards(tb.not(sub.sub(0))));
            } else if (sub.op() == Junctor.OR) {
                return tb.and(pushNegationsInvards(tb.not(sub.sub(0))),
                    pushNegationsInvards(tb.not(sub.sub(1))));
            } else if (sub.op() == Junctor.AND) {
                return tb.or(pushNegationsInvards(tb.not(sub.sub(0))),
                    pushNegationsInvards(tb.not(sub.sub(1))));
            } else if (sub.op() == Junctor.NOT) {
                return pushNegationsInvards(sub.sub(0));
            } else if (sub.op() == Junctor.IMP || sub.op() == Equality.EQV) {
                GeneralUtilities
                        .logErrorAndThrowRTE(LOGGER,
                            "Operator %s not supported by pushNegationInvards, "
                                    + "call eliminateBiImplications before",
                            sub.op());
            }
        }

        return recurse(t, t1 -> pushNegationsInvards(t1));
    }

    /**
     * Splits quantifiers if applicable, that is disjunctions in existentially
     * and conjunctions in universally quantified formulas into two quantified
     * subformulas connected by dis/conjunctions.
     *
     * @param t
     *            The {@link Term} in which to split quantifiers.
     * @return A logically equivalent formula with quantifiers split if
     *         applicable.
     */
    protected Term splitQuantifiers(Term t) {
        // (\exists x; q || p), (\forall x; q && p) to
        // (\exists x; q) || (\exists x; p), (\forall x; q) && (\forall x; p)

        if (t.op() instanceof Quantifier) {
            final QuantifiableVariable qv = t.boundVars().get(0);
            final Term sub = t.sub(0);

            if (t.op() == Quantifier.ALL && sub.op() == Junctor.AND) {
                return tb.and(splitQuantifiers(tb.all(qv, sub.sub(0))),
                    splitQuantifiers(tb.all(qv, sub.sub(1))));
            } else if (t.op() == Quantifier.EX && sub.op() == Junctor.OR) {
                return tb.or(splitQuantifiers(tb.ex(qv, sub.sub(0))),
                    splitQuantifiers(tb.ex(qv, sub.sub(1))));
            }
        }

        return recurse(t, t1 -> splitQuantifiers(t1));
    }

    /**
     * Converts a formula in NNF into CNF (with quantifiers.
     *
     * @param t
     *            The {@link Term} to convert into CNF.
     * @return A logically equivalent {@link Term} to t in CNF (with
     *         quantifiers).
     */
    protected Term applyDistributivityLaws(Term t) {
        // (p && q) || r <==> (p || r) && (q || r)
        // r || (p && q) r <==> (r || p) && (r || q)

        if (t.op() == Junctor.OR) {
            final Term sub1 = t.sub(0);
            final Term sub2 = t.sub(1);

            if (sub1.op() == Junctor.AND) {
                return tb.and(//
                    applyDistributivityLaws(tb.or(sub1.sub(0), sub2)),
                    applyDistributivityLaws(tb.or(sub1.sub(1), sub2)));
            } else if (sub2.op() == Junctor.AND) {
                return tb.and(//
                    applyDistributivityLaws(tb.or(sub1, sub2.sub(0))),
                    applyDistributivityLaws(tb.or(sub1, sub2.sub(1))));
            }
        }

        return recurse(t, t1 -> applyDistributivityLaws(t1));
    }

    private Term recurse(Term t, Function<Term, Term> f) {
        return tf.createTerm(//
            t.op(), //
            new ImmutableArray<Term>(GeneralUtilities.toStream(t.subs())
                    .map(sub -> f.apply(sub)).collect(Collectors.toList())),
            t.boundVars(), t.javaBlock());
    }
}
