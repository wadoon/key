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
class Assignment extends TacletTranslation {
    
    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public Assignment(MethodVisitor mv, ProgVarHelper pvHelper) {
        super(mv, pvHelper);
    }

    @Override
    public void compile(TacletApp app) {
        LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                app, "#loc");
        Expression assgnExpr = (Expression) getTacletAppInstValue(
                app, "#se");

        if (locVar.getKeYJavaType().getJavaType().toString().equals("int")) {

            loadIntVarOrConst(assgnExpr);
            mv().visitVarInsn(ISTORE, pvHelper().progVarNr(locVar));

        } else {
            System.err.println(
                    "[WARNING] Only integer types considered so far, given: "
                            + locVar.getKeYJavaType());
        }
    }

}
