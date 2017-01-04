package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.exceptions.UnexpectedTranslationSituationException;
import de.tud.cs.se.ds.psec.parser.exceptions.UnknownInstructionException;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A super class for instruction elements (that is, (labeled) bytecode
 * instructions).
 *
 * @author Dominic Scheurer
 */
public abstract class Instruction extends TranslationTacletASTElement {
    private static final String UNEXPECTED_TYPE_FOR_LOAD_INSTRUCTION = //
            "Unexpected type for \\load instruction: %s";
    private static final Logger logger = LogManager.getFormatterLogger();

    /**
     * The {@link Instructions} object; this is used for accessing information
     * about loop entry / exit labels.
     */
    private Instructions instructions = null;

    /**
     * Any {@link Instructions} object calling the
     * {@link #translate(MethodVisitor, ProgVarHelper, UniqueLabelManager, RuleInstantiations, Services, List)}
     * method of this {@link Instruction} should call this method before!
     * Otherwise, the compilation of loops will not work.
     * 
     * @param instructions
     *            The {@link Instructions} object containing this
     *            {@link Instruction}.
     */
    void setInstructions(Instructions instructions) {
        this.instructions = instructions;
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
     */
    protected static void loadExpressionToStack(MethodVisitor mv,
            ProgVarHelper pvHelper, Object expr) {
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
            ProgVarHelper pvHelper, Object expr, boolean negative) {
        // We only load Expressions, or Terms that have Expressions as
        // Operators.
        if (expr instanceof Term) {
            Operator op = ((Term) expr).op();
            if (op instanceof Expression) {
                expr = op;
            } else {
                throw new UnexpectedTranslationSituationException(
                        Utilities.format(UNEXPECTED_TYPE_FOR_LOAD_INSTRUCTION,
                                op.getClass().getName()));
            }
        } else if (!(expr instanceof Expression)) {
            throw new UnexpectedTranslationSituationException(
                    Utilities.format(UNEXPECTED_TYPE_FOR_LOAD_INSTRUCTION,
                            expr.getClass().getName()));
        }

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
            // XXX Support more literals

            if (expr instanceof ThisReference) {

                mv.visitVarInsn(ALOAD, 0);

            } else if (expr instanceof Instanceof) {

                Instanceof instOf = (Instanceof) expr;

                LocationVariable obj = (LocationVariable) instOf.getChildAt(0);
                KeYJavaType typeRef = instOf.getTypeReference()
                        .getKeYJavaType();

                mv.visitVarInsn(ALOAD, pvHelper.progVarNr(obj));
                mv.visitTypeInsn(INSTANCEOF,
                        InformationExtraction.toInternalName(typeRef));

            } else if (expr instanceof NullLiteral) {

                mv.visitInsn(ACONST_NULL);

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
