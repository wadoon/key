package de.tud.cs.se.ds.psec.compiler.ast;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
class MethodCallEmptyReturn extends TacletASTNode {
    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public MethodCallEmptyReturn(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, null);
    }

    @Override
    public void compile() {
        mv().visitInsn(RETURN);
    }

}
