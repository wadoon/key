// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Transformer creating the same program a given number of times.
 */
public class RepeatTransformer extends ProgramTransformer {
    private final SchemaVariable countSV;

    public RepeatTransformer(SchemaVariable count, ProgramElement pattern) {
        super("#repeat", pattern);

        assert count != null;
        this.countSV = count;
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        final int count = (int) ((IntLiteral) services.getTypeConverter()
                .getIntegerLDT()
                .translateTerm((Term) svInst.getInstantiation(countSV), null,
                        services)).getValue();
        final ProgramElement[] result = new ProgramElement[count];

        for (int i = 0; i < count; i++) {
            result[i] = pe;
        }

        return result;
    }
}