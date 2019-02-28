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

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * A field location for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class FieldLoc implements AbstrUpdateLHS, AbstrUpdateRHS {
    private final FieldReference fieldReference;
    private final ExecutionContext executionContext;

    public FieldLoc(FieldReference fieldReference,
            ExecutionContext executionContext) {
        this.fieldReference = fieldReference;
        this.executionContext = executionContext;
    }

    @Override
    public Term toRHSTerm(Services services) {
        return services.getTypeConverter()
                .convertVariableReference(fieldReference, executionContext);
    }

    @Override
    public Term toLHSTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final TypeConverter typeConverter = services.getTypeConverter();
        final HeapLDT heapLDT = typeConverter.getHeapLDT();

        final ReferencePrefix prefix = fieldReference.getReferencePrefix();
        final LocationVariable var = (LocationVariable) fieldReference
                .getProgramVariable();

        final Function fieldSymbol = heapLDT
                .getFieldSymbolForPV(var, services);
        return tb.singleton(
                typeConverter.convertReferencePrefix(prefix, executionContext),
                tb.func(fieldSymbol));
    }

}
