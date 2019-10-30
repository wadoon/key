// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
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

import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * @author Dominic Steinhoefel
 *
 */
public class ArrayRange extends HeapLoc {
    final Term array;
    final Term left;
    final Term right;

    public ArrayRange(Term array, Term left, Term right) {
        this.array = array;
        this.left = left;
        this.right = right;
    }

    @Override
    public Set<Operator> childOps() {
        final OpCollector opColl = new OpCollector();
        array.execPostOrder(opColl);
        left.execPostOrder(opColl);
        right.execPostOrder(opColl);
        return opColl.ops();
    }

    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc, Services services) {
        if (otherLoc instanceof AllFieldsLocLHS) {
            return ((AllFieldsLocLHS) otherLoc).getArray().equals(array);
        } else if (otherLoc instanceof PVLoc) {
            return ((PVLoc) otherLoc).getVar()
                    .equals(services.getTypeConverter().getHeapLDT().getHeap());
        } else if (otherLoc instanceof ArrayLoc || otherLoc instanceof ArrayRange) {
            super.mayAssign(otherLoc, services);
        }

        return false;
    }

    @Override
    public Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.arrayRange(array, left, right);
    }

    @Override
    public String toString() {
        return String.format("%s[%s..%s]", array, left, right);
    }

    @Override
    public Sort sort() {
        /*
         * TODO (DS, 2019-10-30): Should be possible to return sort of array elements.
         */
        throw new UnsupportedOperationException();
    }

}
