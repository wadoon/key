// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.logic.op.locs.heap;

import java.util.Optional;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * A "heap location", e.g., a field, array location, or "all fields" array
 * location.
 * 
 * @author Dominic Steinhoefel
 */
public abstract class HeapLocLHS implements AbstractUpdateAssgnLoc {

    /**
     * Applies an update to this {@link HeapLocLHS}. For instance, the application
     * of the update <code>A:=_A</code> on <code>A.*</code> yields
     * <code>_A.*</code>. For program variables, this is not done, but heap objects
     * like fields or array contents are reference types, and therefore this is
     * necessary.
     * 
     * @param proof  The parent {@link Proof} -- for update simplification.
     * @param update The update to apply.
     * @return The new {@link HeapLocLHS}, or an empty optional if the update could
     *         not be applied.
     */
    public Optional<HeapLocLHS> applyUpdate(Proof proof, Term update) {
        final Services services = proof.getServices();

        try {
            final Term termAfterUpdAppl = MergeRuleUtils.simplify(proof,
                    services.getTermBuilder().apply(update, toTerm(services)), 1000);
            final Set<AbstractUpdateAssgnLoc> newLocs = AbstractUpdateFactory
                    .abstrUpdateAssgnLocsFromTermUnsafe(termAfterUpdAppl, Optional.empty(),
                            services);

            if (newLocs == null || newLocs.size() != 1) {
                return Optional.empty();
            } else {
                final AbstractUpdateAssgnLoc elem = newLocs.iterator().next();
                return elem instanceof HeapLocLHS ? Optional.of((HeapLocLHS) elem)
                        : Optional.empty();
            }
        } catch (ProofInputException e) {
            return Optional.empty();
        }
    }

    protected abstract Term toTerm(Services services);

}
