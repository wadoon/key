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

import java.util.Collections;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A program variable location for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class PVLoc implements AbstractUpdateLoc {
    private final LocationVariable loc;

    public PVLoc(LocationVariable loc) {
        this.loc = loc;
    }

    @Override
    public Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.singletonPV(loc);
    }

    @Override
    public Set<Operator> childOps() {
        return Collections.singleton(loc);
    }

    /**
     * @return the encapsulated location.
     */
    public LocationVariable getVar() {
        return loc;
    }

    @Override
    public String toString() {
        return loc.toString();
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof PVLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * loc.hashCode();
    }

    @Override
    public Sort sort() {
        return loc.sort();
    }

    @Override
    public boolean isAbstract() {
        return false;
    }
}