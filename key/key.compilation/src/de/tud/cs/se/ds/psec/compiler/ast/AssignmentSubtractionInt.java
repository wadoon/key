package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Assignment of the form <code>#loc = #seCharByteShortInt0 - #seCharByteShortInt1;</code>.
 *
 * @author Dominic Scheurer
 */
class AssignmentSubtractionInt extends TacletASTNode {
    private static final Logger logger = LogManager.getFormatterLogger();
    
    /**
     * @see TacletASTNode#TacletASTNode(MethodVisitor, ProgVarHelper, TacletApp)
     */
    public AssignmentSubtractionInt(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        logger.trace("Compiling AssignmentSubtractionInt");
        
        LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                "#loc");
        Expression assgnExpr1 = (Expression) getTacletAppInstValue(
                "#seCharByteShortInt0");
        Expression assgnExpr2 = (Expression) getTacletAppInstValue(
                "#seCharByteShortInt1");

        loadIntVarOrConst(assgnExpr1);
        loadIntVarOrConst(assgnExpr2);
        mv().visitInsn(ISUB);
        mv().visitVarInsn(ISTORE, pvHelper().progVarNr(locVar));
        
        compileFirstChild();
    }

}
