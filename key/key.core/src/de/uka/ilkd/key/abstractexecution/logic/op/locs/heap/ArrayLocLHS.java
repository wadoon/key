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

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * An array location for use in an {@link AbstractUpdate} left-hand side.
 *
 * @author Dominic Steinhoefel
 */
public class ArrayLocLHS extends HeapLocLHS {
    private final Term array;
    private final Term index;

    public ArrayLocLHS(Term array, Term index) {
        this.array = array;
        this.index = index;
    }

    @Override
    protected Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.dotArr(array, index);
    }

    /**
     * @return the array
     */
    public Term getArray() {
        return array;
    }

    /**
     * @return the index
     */
    public Term getIndex() {
        return index;
    }

    @Override
    public AbstractUpdateAssgnLoc replaceVariables(Map<ProgramVariable, ProgramVariable> replMap,
            Services services) {
        return this; // TODO?
    }

    @Override
    public Set<Operator> childOps() {
        final OpCollector opColl = new OpCollector();
        array.execPostOrder(opColl);
        index.execPostOrder(opColl);
        return opColl.ops();
    }

    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc) {
        if (otherLoc instanceof AllFieldsLocRHS) {
            /*
             * TODO (DS, 2019-05-22): Check whether that's the intended semantics, since
             * actually, an a[5] cannot really assign a[*], at least not all positions...
             */
            return ((AllFieldsLocRHS) otherLoc).getArray().equals(this.array);
        } else {
            /*
             * TODO (DS, 2019-05-23): Equality might be misleading... Might there be
             * aliasing etc., or does this practically not occur?
             */
            return otherLoc instanceof ArrayLocRHS
                    && ((ArrayLocRHS) otherLoc).getArray().equals(this.array)
                    && ((ArrayLocRHS) otherLoc).getIndex().equals(this.getIndex());
        }
    }

    @Override
    public String toString() {
        return String.format("%s[%s])", array, index);
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof ArrayLocLHS && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 7 * array.hashCode() + 11 * index.hashCode();
    }
}
