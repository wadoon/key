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
 * Represents a function (i.e., a constant of some concrete, non-locset type).
 * Can appear after substituting locations on right-hand sides of abstract
 * updates with some symbols.
 *
 * @author Dominic Steinhoefel
 */
public class FuncRHS extends AbstractSortedOperator implements AbstrUpdateRHS {
    private final Function func;

    public FuncRHS(Function func) {
        super(new Name("funcRHS"), new Sort[] { func.sort() }, func.sort(),
                true);
        assert !func.name().toString().equals("LocSet");
        this.func = func;
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTermBuilder().func(func);
    }

    @Override
    public AbstractUpdateLoc replaceVariables(
            Map<ProgramVariable, ProgramVariable> replMap) {
        return this;
    }

    @Override
    public Operator childOp() {
        return func;
    }

    @Override
    public String toString() {
        return func.toString();
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof FuncRHS && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * func.hashCode();
    }
}
