package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * An instruction to an Integer {@link ProgramVariable} or {@link Literal} onto
 * the stack.
 *
 * @author Dominic Scheurer
 */
public class LoadIntInstruction
        extends Instruction {
    private static final Logger logger = LogManager.getFormatterLogger();

    private String schemaVar;
    private boolean negative;

    /**
     * Constructs a {@link LoadIntInstruction} for loading the element specified
     * in the symbolic execution taclet by the schema variable schemaVar onto
     * the stack. If negative is set, then the element will be negated.
     * 
     * @param schemaVar
     * @param negative
     */
    public LoadIntInstruction(String schemaVar, boolean negative) {
        this.schemaVar = schemaVar;
        this.negative = negative;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            TacletApp app, List<TacletASTNode> children) {
        Expression expr = (Expression) getTacletAppInstValue(app, schemaVar);

        if (expr instanceof IntLiteral) {
            intConstInstruction(mv, (negative ? -1 : 1)
                    * Integer.parseInt(((IntLiteral) expr).toString()));
        }
        else if (expr instanceof LocationVariable) {
            mv.visitVarInsn(ILOAD, pvHelper.progVarNr((LocationVariable) expr));
        }
        else if (expr instanceof Negative) {
            //TODO Is there a double negation case to consider?
            intConstInstruction(mv,
                    -1 * Integer.parseInt(((Negative) expr).getChildAt(0).toString()));
        }
        else {
            logger.error(
                    "Currently not supporting the type %s in assignments, returns etc.",
                    expr.getClass());
            System.exit(1);
        }
    }

}
