package de.tud.cs.se.ds.psec.parser.ast;

import java.util.HashMap;
import java.util.List;
import java.util.Optional;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.tud.cs.se.ds.psec.util.Utilities;
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

        // The locVarSV may either be a SchemaVariable name pointing to a
        // LocationVariable, of an Integer literal for direct usage.

        Optional<Integer> intVal = Utilities.tryParseInt(locVarSV);

        if (intVal.isPresent()) {
            mv.visitVarInsn(opcode, intVal.get());
        } else {
            LocationVariable progVar = (LocationVariable) instantiations
                    .getInstantiationFor(locVarSV).get();
            mv.visitVarInsn(opcode,
                    pvHelper.progVarNr(progVar));
        }

    }

}
