package de.tud.cs.se.ds.psec.parser.ast;

import java.util.HashMap;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.parser.exceptions.SemanticException;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A unary bytecode instruction expecting a label as argument.
 *
 * @author Dominic Scheurer
 */
public class LabelUnaryBytecodeInstr extends Instruction {
    private static final Logger logger = LogManager.getFormatterLogger();
    
    private Label label;
    private int opcode;

    private static final HashMap<String, Integer> OPCODES_MAP = new HashMap<>();

    static {
        OPCODES_MAP.put("GOTO", GOTO);
        OPCODES_MAP.put("IF_ICMPLE", IF_ICMPLE);
        OPCODES_MAP.put("IF_ICMPNE", IF_ICMPNE);
        OPCODES_MAP.put("IFEQ", IFEQ);
        OPCODES_MAP.put("IFNE", IFNE);
    }

    /**
     * @param insn
     *            The bytecode instruction.
     * @param locVarSV
     *            The location variable that is the argument of this
     *            {@link LabelUnaryBytecodeInstr}.
     * @throws SemanticException
     *             if a wrong bytecode instruction is given.
     */
    public LabelUnaryBytecodeInstr(String insn, Label label) {
        this.label = label;
        
        if (!OPCODES_MAP.containsKey(insn)) {
            logger.error("Unknown instruction %s", insn);
            System.exit(1);
        }
        
        opcode = OPCODES_MAP.get(insn);
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            TacletApp app, List<TacletASTNode> children) {

        switch (opcode) {
        case GOTO:
        case IF_ICMPLE:
        case IFEQ:
        case IFNE:
            mv.visitJumpInsn(opcode, label);
            break;
        }

    }

}
