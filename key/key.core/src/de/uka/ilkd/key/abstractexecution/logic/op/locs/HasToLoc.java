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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A has-to location for use in an abstract update.
 *
 * @author Dominic Steinhoefel
 */
public class HasToLoc extends AbstractSortedOperator implements AbstrUpdateLHS {
    private final AbstrUpdateLHS child;

    public HasToLoc(AbstrUpdateLHS child) {
        super(new Name("hasTo"), new Sort[] { child.sort() }, child.sort(),
                child.isRigid());

        assert !(child instanceof HasToLoc);
        assert !(child instanceof AllLocsLoc);

        this.child = child;
    }

    public AbstrUpdateLHS child() {
        return child;
    }

    @Override
    public AbstractUpdateLoc replaceVariables(
            Map<ProgramVariable, ProgramVariable> replMap) {
        return new HasToLoc((AbstrUpdateLHS) child.replaceVariables(replMap));
    }

    @Override
    public Operator childOp() {
        return child.childOp();
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
}
