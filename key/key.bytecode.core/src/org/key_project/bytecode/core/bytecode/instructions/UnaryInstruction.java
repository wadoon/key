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

package org.key_project.bytecode.core.bytecode.instructions;

import org.key_project.bytecode.core.bytecode.Instruction;
import org.key_project.bytecode.core.bytecode.Operand;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public abstract class UnaryInstruction implements Instruction {
    
    private final ImmutableList<Operand> operands;
    
    /**
     * TODO: Document.
     *
     */
    protected UnaryInstruction(Operand operand) {
        this.operands = ImmutableSLList.<Operand>nil().prepend(operand);
    }
    
    protected UnaryInstruction(ImmutableList<Operand> operands) {
        this.operands = operands;
    }
    
    @Override
    public int arity() {
        return 1;
    }

    @Override
    public ImmutableList<Operand> operands() {
        return operands;
    }
    
}
