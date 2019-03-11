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

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A field location for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class FieldLoc implements AbstrUpdateLHS, AbstrUpdateUpdatableLoc {
    private final FieldReference fieldReference;
    private final ExecutionContext executionContext;
    private final LocationVariable heapVar;

    public FieldLoc(FieldReference fieldReference,
            ExecutionContext executionContext, LocationVariable heapVar) {
        this.fieldReference = fieldReference;
        this.executionContext = executionContext;
        this.heapVar = heapVar;
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTypeConverter()
                .convertVariableReference(fieldReference, executionContext);
    }

    @Override
    public AbstractUpdateLoc replaceVariables(
            Map<ProgramVariable, ProgramVariable> replMap) {
        /*
         * TODO (DS, 2019-02-28): Check whether we have to do something with the
         * field reference, i.e., whether a given program variable in the map
         * can represent a field.
         */

        if (replMap.containsKey(heapVar)) {
            return new FieldLoc(fieldReference, executionContext,
                    (LocationVariable) replMap.get(heapVar));
        }

        return this;
    }

    @Override
    public Set<Operator> childOps() {
        final Set<Operator> result = new LinkedHashSet<>();
        result.add(heapVar);
        result.add(fieldReference.getProgramVariable());
        return result;
    }

    @Override
    public AbstrUpdateUpdatableLoc toUpdatableRHS() {
        return this;
    }

    @Override
    public String toString() {
        return fieldReference.toString();
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof FieldLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 7 * executionContext.hashCode()
                + 27 * fieldReference.hashCode();
    }

}
