package de.tud.cs.se.ds.psec.compiler.taclet_translation;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public abstract class NonTerminatingTranslation extends TacletTranslation {

    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public NonTerminatingTranslation(MethodVisitor mv, ProgVarHelper pvHelper) {
        super(mv, pvHelper);
    }

    protected abstract void doCompile(TacletApp app);
    
    @Override
    public boolean compile(TacletApp app) {
        doCompile(app);
        
        return false;
    }
    
}
