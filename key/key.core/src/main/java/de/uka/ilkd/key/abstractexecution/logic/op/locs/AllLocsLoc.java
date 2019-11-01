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
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * The special "allLocs" location.
 *
 * @author Dominic Steinhoefel
 */
public class AllLocsLoc implements AbstractUpdateLoc {
    private final Function allLocs;

    public AllLocsLoc(Function allLocs) {
        this.allLocs = allLocs;
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTermBuilder().func(allLocs);
    }

    @Override
    public Set<Operator> childOps() {
        return Collections.singleton(allLocs);
    }

    @Override
    public String toString() {
        return "allLocs";
    }
    
    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc, Services services) {
        // allLocs can assign everything.
        return true;
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof AllLocsLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * allLocs.hashCode();
    }

    @Override
    public Sort sort() {
        return allLocs.sort();
    }
}
