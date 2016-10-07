package de.tud.cs.se.ds.psec.parser.ast;

import java.util.HashMap;
import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * A unary bytecode instruction expecting a location variable reference as
 * argument.
 *
 * @author Dominic Scheurer
 */
public class LocVarUnaryBytecodeInstr extends Instruction {
    private String locVarSV;
    private int opcode;

    private static final HashMap<String, Integer> OPCODES_MAP = new HashMap<>();

    static {
        OPCODES_MAP.put("ALOAD", ALOAD);
        OPCODES_MAP.put("ASTORE", ASTORE);
        OPCODES_MAP.put("ISTORE", ISTORE);
    }

    /**
     * @param insn
     *            The bytecode instruction.
     * @param locVarSV
     *            The location variable that is the argument of this
     *            {@link LocVarUnaryBytecodeInstr}.
     */
    public LocVarUnaryBytecodeInstr(String insn, String locVarSV) {
        this.locVarSV = locVarSV;
        opcode = OPCODES_MAP.get(insn);
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {

        mv.visitVarInsn(opcode,
                pvHelper.progVarNr((LocationVariable) instantiations
                        .getInstantiationFor(locVarSV).get()));

    }

}
