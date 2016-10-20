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
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * A bytecode {@link Instruction} for a writing access to a field.
 *
 * @author Dominic Scheurer
 */
public class FieldInstr extends Instruction {
    private int opcode;
    private String field;

    private static final HashMap<String, Integer> OPCODES_MAP = new HashMap<>();

    static {
        OPCODES_MAP.put("PUTFIELD", PUTFIELD);
        OPCODES_MAP.put("GETFIELD", GETFIELD);
    }

    /**
     * @param insn
     *            The bytecode instruction.
     * @param locVarSV
     *            The location variable that is the argument of this
     *            {@link FieldInstr}.
     */
    public FieldInstr(String insn, String field) {
        opcode = OPCODES_MAP.get(insn);
        this.field = field;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        LocationVariable fieldRef = (LocationVariable) instantiations
                .getInstantiationFor(field).get();

        writeFieldInsn(opcode, mv, fieldRef);

    }

    /**
     * Writes a field instruction for the given opcode the the
     * {@link LocationVariable} referring to the field to the supplied
     * {@link MethodVisitor}.
     * 
     * @param opcode
     *            The opcode for the field instruction.
     * @param mv
     *            The {@link MethodVisitor} to write to.
     * @param fieldRef
     *            The {@link LocationVariable} referring to the field.
     */
    static void writeFieldInsn(int opcode, MethodVisitor mv,
            LocationVariable fieldRef) {
        mv.visitFieldInsn(opcode,
                InformationExtraction
                        .toInternalName(fieldRef.getContainerType()),
                extractFieldNameFromFQN(fieldRef), //
                InformationExtraction
                        .typeToTypeDescriptor(fieldRef.getKeYJavaType()));
    }

    /**
     * Removes the class name prefix from a field's name, i.e. renders for
     * instance <code>de.tud.test.simple.objects.SimpleObjects::i</code> into
     * <code>i</code>.
     * 
     * @param fieldRef
     *            The field reference to extract the simple name from.
     * @return The simple name of the given field reference, i.e. the name
     *         without the class prefix.
     */
    private static String extractFieldNameFromFQN(IProgramVariable fieldRef) {
        return fieldRef.toString()
                .substring(fieldRef.toString().lastIndexOf(':') + 1);
    }

}
