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

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A program variable location for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class PVLoc extends AbstractSortedOperator
        implements AbstrUpdateLHS, AbstrUpdateUpdatableLoc {
    private final LocationVariable locVar;

    public PVLoc(LocationVariable locVar) {
        super(new Name("pvLoc"), new Sort[] { locVar.sort() }, locVar.sort(),
                false);
        this.locVar = locVar;
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTermBuilder().var(locVar);
    }

    @Override
    public AbstractUpdateLoc replaceVariables(
            Map<ProgramVariable, ProgramVariable> replMap) {
        if (replMap.containsKey(locVar)) {
            return new PVLoc((LocationVariable) replMap.get(locVar));
        } else {
            return this;
        }
    }

    @Override
    public Operator childOp() {
        return locVar;
    }

    @Override
    public String toString() {
        return locVar.toString();
    }

    @Override
    public AbstrUpdateUpdatableLoc toUpdatableRHS() {
        return this;
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof PVLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * locVar.hashCode();
    }
}
