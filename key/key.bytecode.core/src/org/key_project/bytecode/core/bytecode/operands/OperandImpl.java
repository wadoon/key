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
public abstract class OperandImpl implements Operand {

    protected final Term value;

    /**
     * TODO: Document.
     *
     * @param value
     */
    public OperandImpl(Term value) {
        assert value.sort() == type().getSort() : "Value has to be of matching type.";

        this.value = value;
    }

    /**
     * @return the value
     */
    public Term getValue() {
        return value;
    }

}