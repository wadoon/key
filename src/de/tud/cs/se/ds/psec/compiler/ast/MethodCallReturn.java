package de.tud.cs.se.ds.psec.compiler.ast;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
class MethodCallReturn extends TacletASTNode {
    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public MethodCallReturn(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        Expression returnExpr = (Expression) getTacletAppInstValue(
                "#se");

        loadIntVarOrConst(returnExpr);
        mv().visitInsn(IRETURN);
    }

}
