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
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A field location for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class FieldLoc extends AbstractSortedOperator
        implements AbstrUpdateLHS, AbstrUpdateUpdatableLoc {
    private final FieldReference fieldReference;
    private final ExecutionContext executionContext;

    public FieldLoc(FieldReference fieldReference,
            ExecutionContext executionContext) {
        // TODO (DS, 2019-02-28): Check that this is the right sort
        super(new Name("fieldsLoc"),
                new Sort[] { fieldReference.getKeYJavaType().getSort() },
                fieldReference.getKeYJavaType().getSort(), false);
        this.fieldReference = fieldReference;
        this.executionContext = executionContext;
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
        return this;
    }

    @Override
    public Operator childOp() {
        /* TODO (DS, 2019-02-28): Check that this is the right thing to do. */
        return fieldReference.getProgramVariable();
    }

    @Override
    public String toString() {
        // TODO (DS, 2019-02-28): Maybe not what one wants, check
        return String.format("(%s, %s)",
                fieldReference.getReferencePrefix().toString(),
                fieldReference.getIdentifier().toString());
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
