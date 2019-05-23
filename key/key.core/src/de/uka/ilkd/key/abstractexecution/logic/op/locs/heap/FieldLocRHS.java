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

import java.util.Optional;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A field location for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class FieldLocRHS implements HeapLocRHS {
    private final Sort sort;
    private final Optional<Term> heapTerm;
    private final Term objTerm;
    private final LocationVariable fieldPV;

    public FieldLocRHS(Optional<Sort> sort, Optional<Term> heapTerm, Term objTerm,
            LocationVariable fieldPV) {
        this.sort = sort.orElse(fieldPV.sort());
        this.heapTerm = heapTerm;
        this.objTerm = objTerm;
        this.fieldPV = fieldPV;
    }

    /**
     * @return the objTerm
     */
    public Term getObjTerm() {
        return objTerm;
    }

    /**
     * @return the fieldPV
     */
    public LocationVariable getFieldPV() {
        return fieldPV;
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTermBuilder().select(sort,
                heapTerm.orElse(services.getTermBuilder().getBaseHeap()), objTerm, fieldPV);
    }

    @Override
    public String toString() {
        return String.format("%s.%s", objTerm,
                ((ProgramElementName) fieldPV.name()).getProgramName());
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof FieldLocRHS && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 7 * objTerm.hashCode() + 11 * fieldPV.hashCode();
    }

}
