package de.tud.cs.se.ds.psec.parser.ast;

import java.util.HashMap;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.parser.exceptions.UnknownInstructionException;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A unary bytecode instruction expecting a label as argument.
 *
 * @author Dominic Scheurer
 */
public class LabelUnaryBytecodeInstr extends Instruction {
    private static final Logger logger = LogManager.getFormatterLogger();

    private String labelName;
    private int opcode;

    private static final HashMap<String, Integer> OPCODES_MAP = new HashMap<>();

    static {
        OPCODES_MAP.put("GOTO", GOTO);
        OPCODES_MAP.put("IF_ACMPNE", IF_ACMPNE);
        OPCODES_MAP.put("IF_ICMPGE", IF_ICMPGE);
        OPCODES_MAP.put("IF_ICMPLE", IF_ICMPLE);
        OPCODES_MAP.put("IF_ICMPNE", IF_ICMPNE);
        OPCODES_MAP.put("IFEQ", IFEQ);
        OPCODES_MAP.put("IFNE", IFNE);
    }

    /**
     * 
     * @param insn
     *            The bytecode instruction.
     * @param labelName
     *            The name of the label. This name has to be unique per
     *            translation definition.
     */
    public LabelUnaryBytecodeInstr(String insn, String labelName) {
        this.labelName = labelName;

        if (!OPCODES_MAP.containsKey(insn)) {
            String message = Utilities.format("Unknown instruction %s", insn);
            logger.error(message);
            
            throw new UnknownInstructionException(message);
        }

        opcode = OPCODES_MAP.get(insn);
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, TacletApp app, List<TacletASTNode> children) {

        mv.visitJumpInsn(opcode, labelManager.getLabelForName(labelName));

    }

}
