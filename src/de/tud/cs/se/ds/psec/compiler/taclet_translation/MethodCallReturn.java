package de.tud.cs.se.ds.psec.compiler.taclet_translation;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
class MethodCallReturn extends TacletTranslation {
    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public MethodCallReturn(MethodVisitor mv, ProgVarHelper pvHelper) {
        super(mv, pvHelper);
    }

    @Override
    public void compile(TacletApp app) {
        Expression returnExpr = (Expression) getTacletAppInstValue(
                app, "#se");

        loadIntVarOrConst(returnExpr);
        mv().visitInsn(IRETURN);
    }

}
