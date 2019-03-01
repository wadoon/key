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
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Represents a rigid RHG of non-locset type (e.g., some constant). Can appear
 * after substituting locations on right-hand sides of abstract updates with
 * some symbols.
 *
 * @author Dominic Steinhoefel
 */
public class RigidRHS extends AbstractSortedOperator implements AbstrUpdateRHS {
    private final Term t;

    public RigidRHS(Term t) {
        super(new Name("rigidRHS"), new Sort[] { t.sort() }, t.sort(),
                true);
        assert !t.sort().name().toString().equals("LocSet");
        this.t = t;
    }

    @Override
    public Term toTerm(Services services) {
        return t;
    }

    @Override
    public AbstractUpdateLoc replaceVariables(
            Map<ProgramVariable, ProgramVariable> replMap) {
        return this;
    }

    @Override
    public Operator childOp() {
        return t.op();
    }

    @Override
    public String toString() {
        return t.toString();
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof RigidRHS && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * t.hashCode();
    }
}