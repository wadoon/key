package de.tud.cs.se.ds.psec.compiler.taclet_translation;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
class MethodCallEmptyReturn extends TacletTranslation {
    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public MethodCallEmptyReturn(MethodVisitor mv, ProgVarHelper pvHelper) {
        super(mv, pvHelper);
    }

    @Override
    public void compile(TacletApp app) {
        mv().visitInsn(RETURN);
    }

}
