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

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * The special "allLocs" location.
 *
 * @author Dominic Steinhoefel
 */
public class EmptyLoc extends AbstractSortedOperator
        implements AbstrUpdateLHS, AbstrUpdateUpdatableLoc {
    private final Function emptyLocSet;

    public EmptyLoc(Function empty) {
        super(new Name("emptyLoc"), new Sort[] { empty.sort() }, empty.sort(),
                true);
        this.emptyLocSet = empty;
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTermBuilder().func(emptyLocSet);
    }

    @Override
    public AbstractUpdateLoc replaceVariables(
            Map<ProgramVariable, ProgramVariable> replMap) {
        return this;
    }

    @Override
    public Operator childOp() {
        return emptyLocSet;
    }

    @Override
    public String toString() {
        return "empty";
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
