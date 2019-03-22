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

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Creates the wellformedness condition for anonymizing function symbols in the
 * given anonymizing heap update. New symbols in the anonymizing update (like
 * "anon_heap_LOOP") are added to the namespaces. This is because the update is,
 * for the loop scope invariant taclet, created by a variable condition; new
 * symbols created there are not automatically stored in the proof, or will be
 * generated/stored multiple times.
 * 
 * @author Dominic Steinhoefel
 */
public final class CreateWellformedCond extends AbstractTermTransformer {

    public CreateWellformedCond() {
        super(new Name("#wellFormedCond"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {
        final Term anonHeapUpdate = term.sub(0);
        return createWellformedCond(anonHeapUpdate, services);
    }

    /**
     * Extracts from the anonymizing heap update the anonymizing functions and
     * creates a wellformedness condition. Thereby, saves the new functions in
     * the namespaces (which should not have occurred before!).
     * 
     * @param heapAnonUpdate
     *            The anonymizing heap update.
     * @param services
     *            The {@link Services} object.
     * @return The wellformedness condition.
     */
    private Term createWellformedCond(Term heapAnonUpdate, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final List<Term> elems = MergeRuleUtils
                .getElementaryUpdates(heapAnonUpdate, tb);

        Term result = null;
        for (final Term elem : elems) {
            final Operator op = elem.sub(0).op();
            assert op == services.getTypeConverter().getHeapLDT().getAnon();
            final Term anonFunTerm = elem.sub(0).sub(2);

            services.getNamespaces().functions()
                    .addSafely((Function) anonFunTerm.op());

            final Term singleWfTerm = tb.wellFormed(anonFunTerm);
            result = result == null ? singleWfTerm
                    : tb.and(result, singleWfTerm);
        }

        return result;
    }
}