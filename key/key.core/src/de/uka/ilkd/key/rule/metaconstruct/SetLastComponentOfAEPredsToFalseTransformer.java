// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.function.Function;
import java.util.function.Predicate;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Sets the second component of a binary predicate, which may be preceded by a
 * negation operator, to the given term.
 *
 * @author Dominic Steinhoefel
 */
public class SetLastComponentOfAEPredsToFalseTransformer
        extends AbstractTermTransformer {

    public SetLastComponentOfAEPredsToFalseTransformer() {
        super(new Name("#setLastComponentOfAEPredsToFalse"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {
        final Term origTerm = term.sub(0);

        final TermLabel aeLabel = ParameterlessTermLabel.AE_EQUIV_PROOF_LABEL;
        final Sort booleanSort = //
                services.getTypeConverter().getBooleanLDT().targetSort();
        final Predicate<Term> filter = t -> t.containsLabel(aeLabel) && //
                !t.subs().isEmpty() && //
                t.sub(t.subs().size() - 1).sort() == booleanSort;
        final Function<Term, Term> replacer = //
                t -> replaceLastSubByFalse(t, services);

        return GenericTermReplacer.replace( //
                origTerm, filter, replacer, services);
    }

    private static Term replaceLastSubByFalse(Term t, Services services) {
        final Term[] subs = t.subs().toArray(new Term[0]);
        subs[subs.length - 1] = services.getTermBuilder().FALSE();
        return services.getTermFactory().createTerm(t.op(), subs, t.boundVars(),
                t.javaBlock(), t.getLabels());
    }
}