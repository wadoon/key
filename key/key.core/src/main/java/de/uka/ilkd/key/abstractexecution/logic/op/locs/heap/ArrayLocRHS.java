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

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * An array location for use in an {@link AbstractUpdate} left-hand side.
 *
 * @author Dominic Steinhoefel
 */
public class ArrayLocRHS implements HeapLocRHS {
    private final Term array;
    private final Term index;

    public ArrayLocRHS(Term array, Term index) {
        this.array = array;
        this.index = index;
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
    public Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.dotArr(array, index);
    }

    @Override
    public String toString() {
        return String.format("%s[%s])", array, index);
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof ArrayLocRHS && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 7 * array.hashCode() + 11 * index.hashCode();
    }
}
