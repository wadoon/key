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
public abstract class UnaryInstruction<O extends Operand> implements Instruction<O> {
    
    private final ImmutableList<O> operands;
    
    /**
     * TODO: Document.
     *
     */
    protected UnaryInstruction(O operand) {
        this.operands = ImmutableSLList.<O>nil().prepend(operand);
    }
    
    protected UnaryInstruction(ImmutableList<O> operands) {
        this.operands = operands;
    }
    
    @Override
    public int arity() {
        return 1;
    }

    @Override
    public ImmutableList<O> operands() {
        return operands;
    }
    
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        
        sb.append(name())
            .append(" ")
            .append(operands().head());
        
        return sb.toString();
    }
}
