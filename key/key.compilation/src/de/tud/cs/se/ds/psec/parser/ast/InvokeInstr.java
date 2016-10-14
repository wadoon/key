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
import de.uka.ilkd.key.logic.op.IProgramMethod;

/**
 * A bytecode instruction invoking a method that is literally given, i.e. not by
 * a schema variable.
 *
 * @author Dominic Scheurer
 */
public class InvokeInstr extends Instruction {
    private int opcode;

    private String cls;
    private String mname;
    private String sig;

    private String sv;

    private static final HashMap<String, Integer> OPCODES_MAP = new HashMap<>();

    static {
        OPCODES_MAP.put("INVOKESPECIAL", INVOKESPECIAL);
        OPCODES_MAP.put("INVOKESTATIC", INVOKESTATIC);
        OPCODES_MAP.put("INVOKEVIRTUAL", INVOKEVIRTUAL);
    }

    public InvokeInstr(String insn, String sv) {
        opcode = OPCODES_MAP.get(insn);
        this.sv = sv;
    }

    /**
     * @param insn
     *            The bytecode instruction, e.g. <code>INVOKEVIRTUAL</code>.
     * @param cls
     *            The class name, in the format <code>java/lang/String</code>.
     * @param mname
     *            The method name.
     * @param sig
     *            The method signature, e.g.
     *            <code>(ILjava/lang/Object;I)V</code>.
     */
    public InvokeInstr(String insn, String cls, String mname, String sig) {
        opcode = OPCODES_MAP.get(insn);

        this.cls = cls;
        this.mname = mname;
        this.sig = sig;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {

        // TODO this won't work on interfaces.

        if (sv != null) {
            IProgramMethod pm = (IProgramMethod) instantiations
                    .getInstantiationFor(sv).get();
            mv.visitMethodInsn(opcode,
                    InformationExtraction.toInternalName(pm.getContainerType()),
                    pm.isConstructor() ? "<init>" : pm.getName(),
                    InformationExtraction.getMethodTypeDescriptor(pm), false);
        } else {
            mv.visitMethodInsn(opcode, cls, mname, sig, false);
        }

    }

}
