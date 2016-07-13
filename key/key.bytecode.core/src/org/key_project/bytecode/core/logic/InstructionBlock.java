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
 * An instruction block has a program counter and a list of instructions.
 *
 * @author Dominic Scheurer
 */
public class InstructionBlock implements ModalContent<BytecodeSourceElement> {

    private int pc;
    private LinkedList<Instruction<?>> insns = new LinkedList<>();

    private static final InstructionBlock EMPTY_BLOCK = new InstructionBlock(
            new LinkedList<Instruction<?>>());

    /**
     * Construct a new {@link InstructionBlock} with a program counter pointing
     * to the first instruction.
     */
    public InstructionBlock(List<Instruction<?>> insns) {
        this.insns.addAll(insns);
        this.pc = 0;
    }

    /**
     * @return The program counter.
     */
    public int pc() {
        return pc;
    }

    /**
     * Sets the program counter.
     *
     * @param pc
     *            The program counter.
     */
    public void setPc(int pc) {
        assert pc < insns.size();
        this.pc = pc;
    }

    /**
     * @return The instructions list.
     */
    public Instruction<?> insn() {
        return insns.get(pc);
    }

    @Override
    public boolean isEmpty() {
        return insns.isEmpty();
    }

    /**
     * @return The empty instruction block.
     */
    public static InstructionBlock emptyBlock() {
        return EMPTY_BLOCK;
    }

    @Override
    public boolean equalsModRenaming(Object se,
            NameAbstractionTable<BytecodeSourceElement> nat) {
        // TODO implement
        throw new RuntimeException("Method still waiting for implementation");
    }

    @Override
    public String toString() {
        if (isEmpty()) {
            return "";
        }

        final StringBuilder sb = new StringBuilder();
        sb.append("[");

        for (int i = 0; i < insns.size(); i++) {
            if (i == pc) {
                sb.append("# ");
            }
            sb.append(insns.get(i))
                    .append(", ");
        }

        sb.delete(sb.length() - 2, sb.length() - 1);

        sb.append("]");

        return sb.toString();
    }

}
