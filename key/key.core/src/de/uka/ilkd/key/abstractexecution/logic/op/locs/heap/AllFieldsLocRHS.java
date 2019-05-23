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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * An "all fields" array location ("myArray[*]").
 *
 * @author Dominic Steinhoefel
 */
public class AllFieldsLocRHS implements HeapLocRHS {
    private final Term array;

    public AllFieldsLocRHS(Term array) {
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
    public String toString() {
        return String.format("%s.*", array);
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof AllFieldsLocRHS && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 31 + 7 * array.hashCode();
    }
}
