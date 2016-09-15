package de.tud.cs.se.ds.psec.compiler.taclet_translation;

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
class AssignmentAdditionInt extends NonTerminatingTranslation {
    
    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public AssignmentAdditionInt(MethodVisitor mv, ProgVarHelper pvHelper) {
        super(mv, pvHelper);
    }

    @Override
    public void doCompile(TacletApp app) {
        LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                app, "#loc");
        Expression assgnExpr1 = (Expression) getTacletAppInstValue(
                app, "#seCharByteShortInt0");
        Expression assgnExpr2 = (Expression) getTacletAppInstValue(
                app, "#seCharByteShortInt1");

        loadIntVarOrConst(assgnExpr1);
        loadIntVarOrConst(assgnExpr2);
        mv().visitInsn(IADD);
        mv().visitVarInsn(ISTORE, pvHelper().progVarNr(locVar));
    }

}
