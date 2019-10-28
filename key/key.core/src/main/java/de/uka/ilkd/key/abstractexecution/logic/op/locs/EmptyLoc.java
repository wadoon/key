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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * The special "allLocs" location.
 *
 * @author Dominic Steinhoefel
 */
public class EmptyLoc implements AbstractUpdateAssgnLoc, AbstractUpdateLoc {
    private final Function emptyLocSet;

    public EmptyLoc(Function empty) {
        this.emptyLocSet = empty;
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTermBuilder().func(emptyLocSet);
    }

    @Override
    public Set<Operator> childOps() {
        return Collections.singleton(emptyLocSet);
    }

    @Override
    public String toString() {
        return "empty";
    }

    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc, Services services) {
        return false;
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof EmptyLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * emptyLocSet.hashCode();
    }
}
