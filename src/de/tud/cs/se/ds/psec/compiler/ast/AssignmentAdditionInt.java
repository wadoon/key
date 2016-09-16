package de.tud.cs.se.ds.psec.compiler.ast;

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
class AssignmentAdditionInt extends TacletASTNode {

    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public AssignmentAdditionInt(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                "#loc");
        Expression assgnExpr1 = (Expression) getTacletAppInstValue(
                "#seCharByteShortInt0");
        Expression assgnExpr2 = (Expression) getTacletAppInstValue(
                "#seCharByteShortInt1");

        loadIntVarOrConst(assgnExpr1);
        loadIntVarOrConst(assgnExpr2);
        mv().visitInsn(IADD);
        mv().visitVarInsn(ISTORE, pvHelper().progVarNr(locVar));
        
        compileFirstChild();
    }

}
