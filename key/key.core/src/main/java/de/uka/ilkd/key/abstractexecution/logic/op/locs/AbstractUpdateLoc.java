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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sorted;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * A left-hand side of an abstract update.
 *
 * @author Dominic Steinhoefel
 */
public interface AbstractUpdateLoc extends Sorted {
    /**
     * All {@link AbstractUpdateLoc}s are containers. This method returns the "real"
     * KeY {@link Operator}s which they represent.
     *
     * @return The KeY {@link Operator}s that this {@link AbstractUpdateLoc}
     *         container represents.
     */
    Set<Operator> childOps();

    /**
     * @param services The {@link Services} object.
     * @return A LocSet term corresponding to this location.
     */
    Term toTerm(Services services);

    /**
     * Some {@link AbstractUpdateLoc}s are not really abstract, e.g., FieldLocs,
     * PVLocs, EmptyLocs. For those, this method return false. For location that
     * describe more than one concrete element, like SkolemLocs or AlllFieldsLocs,
     * it returns true.
     * 
     * @return true iff this location describes a non-trivial set of concrete
     *         locations.
     */
    boolean isAbstract();
}
