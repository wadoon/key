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
package de.uka.ilkd.key.abstractexecution.logic.op.locs.heap;

import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * An "all fields" array location ("myArray[*]").
 *
 * @author Dominic Steinhoefel
 */
public class AllFieldsLocLHS extends HeapLocLHS {
    private final Term array;

    public AllFieldsLocLHS(Term array) {
        this.array = array;
    }

    /**
     * @return the array
     */
    public Term getArray() {
        return array;
    }

    @Override
    public Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.allFields(array);
    }

    @Override
    public AbstractUpdateAssgnLoc replaceVariables(Map<ProgramVariable, ProgramVariable> replMap,
            Services services) {
        return new AllFieldsLocLHS(GenericTermReplacer.replace(array,
                t -> t.op() instanceof ProgramVariable && replMap.containsKey(t.op()),
                t -> services.getTermBuilder().var(replMap.get((ProgramVariable) t.op())),
                services));
    }

    @Override
    public Set<Operator> childOps() {
        final OpCollector opColl = new OpCollector();
        array.execPostOrder(opColl);
        return opColl.ops();
    }

    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc, Services services) {
        if (otherLoc instanceof ArrayLocRHS) {
            return ((ArrayLocRHS) otherLoc).getArray().equals(this.array);
        } else if (otherLoc instanceof PVLoc) {
            return ((PVLoc) otherLoc).getVar()
                    .equals(services.getTypeConverter().getHeapLDT().getHeap());
        } else if (otherLoc instanceof AllFieldsLocRHS) {
            return ((AllFieldsLocRHS) otherLoc).getArray().equals(this.array);
        } else if (otherLoc instanceof ArrayRange) {
            super.mayAssign(otherLoc, services);
        }
        
        return false;
    }

    @Override
    public String toString() {
        return String.format("%s.*", array);
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof AllFieldsLocLHS && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 31 + 7 * array.hashCode();
    }
}
