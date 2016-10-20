package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * An instruction to an Integer {@link ProgramVariable} or {@link Literal} onto
 * the stack.
 *
 * @author Dominic Scheurer
 */
public class LoadInstruction extends Instruction {
    private String schemaVar;
    private boolean negative;

    /**
     * Constructs a {@link LoadInstruction} for loading the element specified in
     * the symbolic execution taclet by the schema variable schemaVar onto the
     * stack. If negative is set, then the element will be negated.
     * 
     * @param schemaVar
     * @param negative
     */
    public LoadInstruction(String schemaVar, boolean negative) {
        this.schemaVar = schemaVar;
        this.negative = negative;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        loadExpressionToStack(mv, pvHelper,
                instantiations.getInstantiationFor(schemaVar).get(), negative);
    }

}
