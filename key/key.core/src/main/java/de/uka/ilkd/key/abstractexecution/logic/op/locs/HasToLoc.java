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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A has-to location for use in an abstract update.
 *
 * @author Dominic Steinhoefel
 */
public class HasToLoc<L extends AbstractUpdateLoc> implements AbstractUpdateLoc {
    private final L child;

    @SuppressWarnings("unchecked")
    public HasToLoc(L child) {
        assert !(child instanceof AllLocsLoc);

        if (child instanceof HasToLoc) {
            this.child = (L) ((HasToLoc<L>) child).child;
        } else {
            this.child = child;
        }
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTermBuilder().hasTo(child.toTerm(services));
    }

    public L child() {
        return child;
    }

    @Override
    public Set<Operator> childOps() {
        return child.childOps();
    }

    @Override
    public String toString() {
        return String.format("hasTo(%s)", child.toString());
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof HasToLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * child.hashCode();
    }

    @Override
    public Sort sort() {
        return child.sort();
    }
    
    @Override
    public boolean isAbstract() {
        return child.isAbstract();
    }
}