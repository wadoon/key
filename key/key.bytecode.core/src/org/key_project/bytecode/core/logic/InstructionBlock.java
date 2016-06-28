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

import org.key_project.bytecode.core.bytecode.BytecodeSourceElement;
import org.key_project.bytecode.core.bytecode.Instruction;
import org.key_project.common.core.logic.ModalContent;
import org.key_project.common.core.program.NameAbstractionTable;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class InstructionBlock implements ModalContent<BytecodeSourceElement> {

    private int pc;
    private LinkedList<Instruction> insns;

    private static InstructionBlock EMPTY_BLOCK = new InstructionBlock(
            new LinkedList<Instruction>());

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

    @Override
    public boolean isEmpty() {
        return insns.isEmpty();
    }

    public static InstructionBlock emptyBlock() {
        return EMPTY_BLOCK;
    }

    @Override
    public boolean equalsModRenaming(Object se,
            NameAbstractionTable<BytecodeSourceElement> nat) {
        // TODO implement
        throw new RuntimeException("Method still waiting for implementation");
    }

}
