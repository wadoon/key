package de.tud.cs.se.ds.psec.parser.ast;

import java.util.HashMap;
import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A bytecode {@link Instruction} for a writing access to a field.
 *
 * @author Dominic Scheurer
 */
public class FieldInstr extends Instruction {
    private int opcode;
    private String object;
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
    public FieldInstr(String insn, String object, String field) {
        opcode = OPCODES_MAP.get(insn);

        this.object = object;
        this.field = field;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, TacletApp app, Services services,
            List<TacletASTNode> children) {

        // TODO Support more taclets than assignment_write_attribute_this, and
        // then of course also other types for objRef here.

        // objRef is currently not used, because it's always "this" so far.
        // Probably extend this in the future.
//        ThisReference objRef = (ThisReference) getTacletAppInstValue(app,
//                object);
        LocationVariable fieldRef = (LocationVariable) getTacletAppInstValue(
                app, field);
        
        //@formatter:off
        mv.visitFieldInsn(opcode,
                InformationExtraction
                        .toInternalName(fieldRef.getContainerType()),
                extractFieldNameFromFQN(fieldRef),
                InformationExtraction
                        .typeToTypeDescriptor(fieldRef.getKeYJavaType()));
        //@formatter:on
        
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
    private String extractFieldNameFromFQN(LocationVariable fieldRef) {
        return fieldRef.toString()
                .substring(fieldRef.toString().lastIndexOf(':') + 1);
    }

}
