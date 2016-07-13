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

import org.key_project.bytecode.core.bytecode.Operand;
import org.key_project.bytecode.core.logic.Term;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class IntOperand extends OperandImpl implements Operand {

    /**
     * TODO: Document.
     *
     * @param value
     */
    public IntOperand(Term value) {
        super(value);
    }

}
