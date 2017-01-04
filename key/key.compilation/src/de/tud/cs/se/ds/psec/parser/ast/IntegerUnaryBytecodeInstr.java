package de.tud.cs.se.ds.psec.parser.ast;

import java.util.HashMap;
import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.GlobalLabelHelper;
import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;

/**
 * A unary bytecode instruction expecting an integer as argument.
 *
 * @author Dominic Scheurer
 */
public class IntegerUnaryBytecodeInstr extends Instruction {
    private int arg;
    private int opcode;

    private static final HashMap<String, Integer> OPCODES_MAP = new HashMap<>();

    static {
        OPCODES_MAP.put("BIPUSH", ISTORE);
    }

    /**
     * @param insn
     *            The bytecode instruction.
     * @param locVarSV
     *            The location variable that is the argument of this
     *            {@link IntegerUnaryBytecodeInstr}.
     */
    public IntegerUnaryBytecodeInstr(String insn, int arg) {
        this.arg = arg;
        opcode = OPCODES_MAP.get(insn);
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            GlobalLabelHelper globalLabelHelper, UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {

        switch (opcode) {
        case BIPUSH:
            mv.visitIntInsn(opcode, arg);
            break;
        }

    }

}
