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
    private final LocationVariable locVar;

    public PVLoc(LocationVariable locVar) {
        this.locVar = locVar;
    }

    @Override
    public Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.singletonPV(tb.var(locVar));
    }

    @Override
    public Set<Operator> childOps() {
        return Collections.singleton(locVar);
    }

    /**
     * @return the encapsulated location variable.
     */
    public LocationVariable getVar() {
        return locVar;
    }

    @Override
    public String toString() {
        return locVar.toString();
    }

    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc, Services services) {
        return otherLoc instanceof PVLoc && otherLoc.equals(this);
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof PVLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * locVar.hashCode();
    }

    @Override
    public Sort sort() {
        return locVar.sort();
    }
}
