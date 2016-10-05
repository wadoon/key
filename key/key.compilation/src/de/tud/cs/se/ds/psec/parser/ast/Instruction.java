package de.tud.cs.se.ds.psec.parser.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.parser.exceptions.UnknownInstructionException;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A super class for instruction elements (that is, (labeled) bytecode
 * instructions).
 *
 * @author Dominic Scheurer
 */
public abstract class Instruction extends TranslationTacletASTElement {
    private static final Logger logger = LogManager.getFormatterLogger();

    /**
     * Loads the given {@link Expression} to the stack. Supports
     * {@link ProgramVariable}s and literal {@link Expression}s.
     * 
     * @param mv
     *            The {@link MethodVisitor} for writing instructions.
     * @param pvHelper
     *            The {@link ProgVarHelper} for obtaining indices for
     *            {@link ProgramVariable}s.
     * @param expr
     *            The {@link Expression} to load onto the stack.
     */
    protected static void loadExpressionToStack(MethodVisitor mv,
            ProgVarHelper pvHelper, Expression expr) {
        loadExpressionToStack(mv, pvHelper, expr, false);
    }

    /**
     * Loads the given {@link Expression} to the stack. Supports
     * {@link ProgramVariable}s and literal {@link Expression}s.
     * 
     * @param mv
     *            The {@link MethodVisitor} for writing instructions.
     * @param pvHelper
     *            The {@link ProgVarHelper} for obtaining indices for
     *            {@link ProgramVariable}s.
     * @param expr
     *            The {@link Expression} to load onto the stack.
     * @param negative
     *            Determines whether an {@link IntLiteral} should be inverted.
     */
    protected static void loadExpressionToStack(MethodVisitor mv,
            ProgVarHelper pvHelper, Expression expr, boolean negative) {
        if (expr instanceof LocationVariable) {

            // Location variables of primitive or object types

            LocationVariable locVar = (LocationVariable) expr;
            if (locVar.getKeYJavaType()
                    .getJavaType() instanceof PrimitiveType) {
                // Location variables of primitive types
                mv.visitVarInsn(ILOAD, pvHelper.progVarNr(locVar));
            } else {
                // Location variables of object types
                mv.visitVarInsn(ALOAD, pvHelper.progVarNr(locVar));
            }

        } else {

            // Literals
            // XXX Support other literals, like null

            if (expr instanceof ThisReference) {

                mv.visitVarInsn(ALOAD, 0);

            } else if (expr instanceof IntLiteral) {

                intConstInstruction(mv, (negative ? -1 : 1)
                        * Integer.parseInt(((IntLiteral) expr).toString()));

            } else if (expr instanceof BooleanLiteral) {

                BooleanLiteral bExpr = (BooleanLiteral) expr;
                if (bExpr.toString().equals("false")) {
                    mv.visitInsn(ICONST_0);
                } else if (bExpr.toString().equals("true")) {
                    mv.visitInsn(ICONST_1);
                } else {
                    logger.error("Unexpected value for BooleanLiteral: %s",
                            bExpr);
                }

            } else if (expr instanceof Negative) {

                // TODO Is there a double negation case to consider?
                intConstInstruction(mv, -1 * Integer
                        .parseInt(((Negative) expr).getChildAt(0).toString()));

            } else {
                String message = Utilities.format(
                        "Currently not supporting the type %s in assignments, returns etc.",
                        expr.getClass());
                logger.error(message);

                throw new UnknownInstructionException(message);
            }

        }
    }
    
}
