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

package org.key_project.bytecode.core.logic;

import java.util.LinkedList;
import java.util.List;

import org.key_project.bytecode.core.ast.Instruction;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class InstructionBlock {
    
    private int pc;
    private LinkedList<Instruction> insns;
    
    /**
     * 
     * TODO: Document.
     *
     */
    public InstructionBlock(List<Instruction> insns) {
       this.insns.addAll(insns);
       this.pc = 0;
    }
    
    /**
     * TODO: Document.
     *
     * @return
     */
    public int pc() {
        return pc;
    }
    
    /**
     * TODO: Document.
     *
     * @return
     */
    public Instruction insn() {
        return insns.get(pc);
    }
    
}
