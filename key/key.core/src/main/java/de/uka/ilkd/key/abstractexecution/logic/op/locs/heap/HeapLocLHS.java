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

import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * A "heap location", e.g., a field, array location, or "all fields" array
 * location.
 * 
 * @author Dominic Steinhoefel
 */
public abstract class HeapLocLHS implements AbstractUpdateLoc {
    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc, Services services) {
        if (otherLoc instanceof PVLoc) {
            final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
            return ((PVLoc) otherLoc).getVar().equals(baseHeap);
        }

        /*
         * TODO (DS, 2019-05-27): We might fail to prove the disjointness condition
         * although it actually holds; for instance, we might need premises from the
         * current proof situation, or there is some basic prover incapacity. We have to
         * check what the implications of such "false negatives" are, and to ensure that
         * they are not critical for soundness.
         */

        final TermBuilder tb = services.getTermBuilder();

        final Term disjointTerm = //
                tb.disjoint(toTerm(services), otherLoc.toTerm(services));

        return MergeRuleUtils.isProvableWithSplitting( //
                disjointTerm, services, 1000);
    }

    /**
     * Converts this {@link HeapLocLHS} to a term representation.
     * 
     * @param services The {@link Services} object.
     * @return A term representation of this {@link HeapLocLHS}, sort is LocSet.
     */
    public abstract Term toTerm(Services services);

}
