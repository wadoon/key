package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * An instruction to store a value in a program variable.
 *
 * @author Dominic Scheurer
 */
public class StoreInstruction extends Instruction {
    private String schemaVar;

    /**
     * Constructs a {@link StoreInstruction} for loading the element specified in
     * the symbolic execution taclet by the schema variable schemaVar onto the
     * stack. If negative is set, then the element will be negated.
     * 
     * @param schemaVar
     */
    public StoreInstruction(String schemaVar) {
        this.schemaVar = schemaVar;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        IProgramVariable locVar = (IProgramVariable) instantiations
                .getInstantiationFor(schemaVar).get();
        
        if (locVar.getKeYJavaType()
                .getJavaType() instanceof PrimitiveType) {
            // Location variables of primitive types
            mv.visitVarInsn(ISTORE, pvHelper.progVarNr(locVar));
        } else {
            // Location variables of object types
            mv.visitVarInsn(ASTORE, pvHelper.progVarNr(locVar));
        }
    }

}
