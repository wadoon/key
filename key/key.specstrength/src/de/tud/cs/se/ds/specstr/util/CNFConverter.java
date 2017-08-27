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
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class CNFConverter {
    private static final Logger logger = LogManager.getFormatterLogger();
    private TermBuilder tb;
    private TermFactory tf;

    /**
     * 
     * @param tb
     */
    public CNFConverter(TermBuilder tb) {
        this.tb = tb;
        this.tf = tb.tf();
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    public Term convertToCNF(Term t) {
        List<Term> updates = null;

        if (t.op() instanceof UpdateApplication) {
            updates = LogicUtilities.getUpdates(t);
        }

        final Term cnfMatrix = applyDistributivityLaws(
                splitQuantifiers(pushNegationsInvards(eliminateBiImplications(
                        TermBuilder.goBelowUpdates(t)))));

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

    protected Term eliminateBiImplications(Term t) {
        if (t.op() == Junctor.IMP) {
            return tb.or(tb.not(eliminateBiImplications(t.sub(0))),
                    eliminateBiImplications(t.sub(1)));
        } else if (t.op() == Equality.EQV) {
            return tb.and(
                    tb.or( //
                            tb.not(eliminateBiImplications(t.sub(0))),
                            eliminateBiImplications(t.sub(1))),
                    tb.or( //
                            tb.not(eliminateBiImplications(t.sub(1))),
                            eliminateBiImplications(t.sub(0))));
        } else {
            return recurse(t, t1 -> eliminateBiImplications(t1));
        }
    }

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
                GeneralUtilities.logErrorAndThrowRTE(logger,
                        "Operator %s not supported by pushNegationInvards, "
                                + "call eliminateBiImplications before",
                        sub.op());
            }
        }

        return recurse(t, t1 -> pushNegationsInvards(t1));
    }

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

    protected Term applyDistributivityLaws(Term t) {
        // (p && q) || r <==> (p || r) && (q || r)
        // r || (p && q) r <==> (r || p) && (r || q)

        if (t.op() == Junctor.OR) {
            final Term sub1 = t.sub(0);
            final Term sub2 = t.sub(1);

            if (sub1.op() == Junctor.AND) {
                return tb.and( //
                        applyDistributivityLaws(tb.or(sub1.sub(0), sub2)),
                        applyDistributivityLaws(tb.or(sub1.sub(1), sub2)));
            } else if (sub2.op() == Junctor.AND) {
                return tb.and( //
                        applyDistributivityLaws(tb.or(sub1, sub2.sub(0))),
                        applyDistributivityLaws(tb.or(sub1, sub2.sub(1))));
            }
        }

        return recurse(t, t1 -> applyDistributivityLaws(t1));
    }

    private Term recurse(Term t, Function<Term, Term> f) {
        return tf.createTerm( //
                t.op(), //
                new ImmutableArray<Term>(GeneralUtilities.toStream(t.subs())
                        .map(sub -> f.apply(sub)).collect(Collectors.toList())),
                t.boundVars(), t.javaBlock());
    }
}
