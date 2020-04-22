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
public abstract class HeapLoc implements AbstractUpdateLoc {

    /**
     * Converts this {@link HeapLoc} to a term representation.
     * 
     * @param services The {@link Services} object.
     * @return A term representation of this {@link HeapLoc}, sort is LocSet.
     */
    public abstract Term toTerm(Services services);

}
