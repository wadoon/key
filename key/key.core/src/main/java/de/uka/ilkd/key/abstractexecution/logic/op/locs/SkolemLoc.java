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

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A Skolem location set suitable for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class SkolemLoc implements AbstractUpdateLoc {
    private final Term skLoc;

    public SkolemLoc(Term skLoc) {
        this.skLoc = skLoc;
    }

    @Override
    public Term toTerm(Services services) {
        return skLoc;
    }

    @Override
    public Set<Operator> childOps() {
        final OpCollector opColl = new OpCollector();
        skLoc.execPostOrder(opColl);
        return opColl.ops();
    }

    @Override
    public String toString() {
        return skLoc.toString();
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof SkolemLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * skLoc.hashCode();
    }

    @Override
    public Sort sort() {
        return skLoc.sort();
    }

    @Override
    public boolean isAbstract() {
        return true;
    }
}
