package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * An assignment of the form <code>#loc = -#seCharByteShortInt;</code>
 *
 * @author Dominic Scheurer
 */
class UnaryMinusInt extends TacletASTNode {
    private static final Logger logger = LogManager.getFormatterLogger();

    /**
     * @see TacletASTNode#TacletASTNode(MethodVisitor, ProgVarHelper, TacletApp)
     */
    public UnaryMinusInt(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        logger.trace("Compiling UnaryMinusInt");
        
        LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                "#loc");
        Expression assgnExpr = (Expression) getTacletAppInstValue(
                "#seCharByteShortInt");

        if (assgnExpr instanceof LocationVariable) {
            mv().visitVarInsn(ILOAD,
                    pvHelper().progVarNr((LocationVariable) assgnExpr));
            mv().visitInsn(INEG);
        } else if (assgnExpr instanceof IntLiteral) {
            loadIntVarOrConst(assgnExpr, true);
        } else {
            logger.error(
                    "Unknown expression type for right-hand side of assignment: %s",
                    assgnExpr.getClass());
            System.exit(1);
        }

        mv().visitVarInsn(ISTORE, pvHelper().progVarNr(locVar));
        
        compileFirstChild();
    }

    @Override
    protected int maxNumberOfChildren() {
        return 1;
    }

}
