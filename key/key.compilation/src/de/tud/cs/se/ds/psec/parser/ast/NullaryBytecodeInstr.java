package de.tud.cs.se.ds.psec.parser.ast;

import java.util.HashMap;
import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A unary bytecode instruction without arguments.
 *
 * @author Dominic Scheurer
 */
public class NullaryBytecodeInstr extends Instruction {
    private int opcode;

    private static final HashMap<String, Integer> OPCODES_MAP = new HashMap<>();

    static {
        OPCODES_MAP.put("IADD", IADD);
        OPCODES_MAP.put("IRETURN", IRETURN);
        OPCODES_MAP.put("ISUB", ISUB);
        OPCODES_MAP.put("RETURN", RETURN);
        OPCODES_MAP.put("ICONST_M1", ICONST_M1);
        OPCODES_MAP.put("ICONST_0", ICONST_0);
        OPCODES_MAP.put("ICONST_1", ICONST_1);
        OPCODES_MAP.put("ICONST_2", ICONST_2);
        OPCODES_MAP.put("ICONST_3", ICONST_3);
        OPCODES_MAP.put("ICONST_4", ICONST_4);
        OPCODES_MAP.put("ICONST_5", ICONST_5);
    }

    /**
     * @param insn
     *            The bytecode instruction.
     */
    public NullaryBytecodeInstr(String insn) {
        opcode = OPCODES_MAP.get(insn);
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            TacletApp app, List<TacletASTNode> children) {

        mv.visitInsn(opcode);

    }

}
