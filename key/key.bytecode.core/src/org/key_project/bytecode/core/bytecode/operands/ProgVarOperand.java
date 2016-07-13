// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.bytecode.core.bytecode.operands;

import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.logic.op.ProgramVariable;

/**
 * Operand referring to a program variable (like needed for ISTORE, for
 * instance). In classic Bytecode, this is an index number; in BytecodeDL, it is
 * a program variable.
 *
 * @author Dominic Scheurer
 */
public class ProgVarOperand extends OperandImpl {

    /**
     * TODO: Document.
     *
     * @param value
     */
    public ProgVarOperand(Term value) {
        super(value);

        assert value
                .op() instanceof ProgramVariable : "Expecting a program variable for instantiation of ProgVarOperand";
    }

}
