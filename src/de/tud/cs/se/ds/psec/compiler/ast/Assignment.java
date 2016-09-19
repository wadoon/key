package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
class Assignment extends TacletASTNode {
    private static final Logger logger = LogManager.getFormatterLogger();
    
    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public Assignment(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        logger.trace("Compiling Assignment");
        
        LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                "#loc");
        Expression assgnExpr = (Expression) getTacletAppInstValue(
                "#se");

        String javaTypeName = locVar.getKeYJavaType().getJavaType().toString();
        if (javaTypeName.equals("int")) {

            loadIntVarOrConst(assgnExpr);

        } else if (javaTypeName.equals("boolean")) {

            loadBooleanVarOrConst(assgnExpr);

        } else {
            unsupportedTypeError("integer and boolean ",
                    locVar.getKeYJavaType());
            return;
        }

        mv().visitVarInsn(ISTORE, pvHelper().progVarNr(locVar));
        
        compileFirstChild();
    }
}
