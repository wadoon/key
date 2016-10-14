package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * An instruction to an Integer {@link ProgramVariable} or {@link Literal} onto
 * the stack.
 *
 * @author Dominic Scheurer
 */
public class ParamsLoadInstruction extends Instruction {
    private String schemaVar;

    /**
     * Constructs a {@link ParamsLoadInstruction} for loading the element
     * specified in the symbolic execution taclet by the schema variable
     * schemaVar onto the stack. If negative is set, then the element will be
     * negated.
     * 
     * @param schemaVar
     * @param negative
     */
    public ParamsLoadInstruction(String schemaVar) {
        this.schemaVar = schemaVar;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        Iterable<?> params = (Iterable<?>) instantiations
                .getInstantiationFor(schemaVar).get();

        params.forEach(param -> loadExpressionToStack(mv, pvHelper,
                param instanceof Term ? (Expression) ((Term) param).op()
                        : (Expression) param));
    }

}
