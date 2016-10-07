package de.tud.cs.se.ds.psec.parser.ast;

import java.util.HashMap;
import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.TypeRef;

/**
 * A unary bytecode type {@link Instruction} expecting a non-trivial type as
 * argument.
 *
 * @author Dominic Scheurer
 */
public class TypeInstr extends Instruction {
    private String arg;
    private int opcode;

    private static final HashMap<String, Integer> OPCODES_MAP = new HashMap<>();

    static {
        OPCODES_MAP.put("CHECKCAST", CHECKCAST);
    }

    /**
     * @param insn
     *            The bytecode instruction.
     * @param locVarSV
     *            The location variable that is the argument of this
     *            {@link TypeInstr}.
     */
    public TypeInstr(String insn, String arg) {
        this.arg = arg;
        opcode = OPCODES_MAP.get(insn);
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations, Services services,
            List<TacletASTNode> children) {

        TypeRef type = (TypeRef) instantiations.getInstantiationFor(arg).get();
        mv.visitTypeInsn(opcode,
                InformationExtraction.toInternalName(type.getKeYJavaType()));

    }

}
