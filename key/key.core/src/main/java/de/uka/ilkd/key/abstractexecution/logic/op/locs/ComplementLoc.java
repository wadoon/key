// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.logic.op.locs;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A location set representing the complement of another one.
 * 
 * @author Dominic Steinhoefel
 */
public class ComplementLoc<L extends AbstractUpdateLoc> implements AbstractUpdateLoc {
    private final L child;

    public ComplementLoc(final L child) {
        this.child = child;
    }

    @Override
    public Sort sort() {
        throw new UnsupportedOperationException("Cannot specify sort of ComplementLoc");
    }

    @Override
    public Set<Operator> childOps() {
        return child.childOps();
    }

    @Override
    public Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.setMinus(tb.allLocs(), child.toTerm(services));
    }

    @Override
    public boolean isAbstract() {
        return true;
    }

}
