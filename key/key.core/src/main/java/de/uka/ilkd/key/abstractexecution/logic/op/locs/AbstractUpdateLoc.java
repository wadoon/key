// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.logic.op.locs;

import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.AllFieldsLocLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.ArrayLocLHS;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * A left-hand side of an abstract update.
 *
 * @author Dominic Steinhoefel
 */
public interface AbstractUpdateLoc {
    /**
     * All {@link AbstractUpdateLoc}s are containers. This method returns the "real"
     * KeY {@link Operator}s which they represent.
     *
     * @return The KeY {@link Operator}s that this {@link AbstractUpdateLoc}
     *         container represents.
     */
    Set<Operator> childOps();

    /**
     * Evaluates whether this {@link AbstractUpdateLoc} may assign otherLoc.
     * This is the case, for instance, if this {@link AbstractUpdateLoc} is a
     * {@link PVLoc} assigning the program variable of otherLoc which is also a
     * {@link PVLoc}; but also, if otherLoc is an {@link ArrayLocLHS} for array A
     * and this {@link AbstractUpdateLoc} is an {@link AllFieldsLocLHS} for A.
     *
     * XXX (DS, 2019-10-28): Have to make the semantics of this more precise. What
     * about a program variable that may assign (part of) an abstract Skolem
     * location set? At the end, it will have to be an overapproximation, i.e., only
     * return false if it's really sure that this operator does not change the
     * valuation of the other one. Example would be to PVLocs with different names.
     * 
     * @param otherLoc The location for which to evaluate whether we can assign it.
     * @param services The {@link Services} object.
     * @return true if this {@link AbstractUpdateLoc} may assign otherLoc.
     */
    boolean mayAssign(AbstractUpdateLoc otherLoc, Services services);

    /**
     * @param services The {@link Services} object.
     * @return A LocSet term corresponding to this location.
     */
    Term toTerm(Services services);
}
