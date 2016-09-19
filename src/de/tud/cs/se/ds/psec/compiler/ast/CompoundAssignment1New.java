package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Assignment of the form <code>#lhs = !#boolExpr</code>.
 *
 * @author Dominic Scheurer
 */
class CompoundAssignment1New extends TacletASTNode {
    private static final Logger logger = LogManager.getFormatterLogger();
    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public CompoundAssignment1New(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        logger.trace("Compiling CompoundAssignment1New");
        
        LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                "#lhs");
        Expression assgnExpr = (Expression) getTacletAppInstValue(
                "#seBool");

        // Load expression
        loadBooleanVarOrConst(assgnExpr);

        // Negate it
        Label l1 = new Label();
        mv().visitJumpInsn(IFEQ, l1);
        
        mv().visitInsn(ICONST_0);
        
        Label l2 = new Label();
        mv().visitJumpInsn(GOTO, l2);
        
        mv().visitLabel(l1);
        mv().visitInsn(ICONST_1);

        // Store negated result
        mv().visitLabel(l2);
        mv().visitVarInsn(ISTORE, pvHelper().progVarNr(locVar));
        
        compileFirstChild();
    }
    
}
