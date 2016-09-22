package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A <code>return;</code> statement without argument.
 *
 * @author Dominic Scheurer
 */
public class MethodCallEmptyReturn extends TacletASTNode {
    private static final Logger logger = LogManager.getFormatterLogger();
    
    /**
     * @see TacletASTNode#TacletASTNode(MethodVisitor, ProgVarHelper, TacletApp)
     */
    public MethodCallEmptyReturn(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, null);
    }

    @Override
    public void compile() {
        logger.trace("Compiling MethodCallEmptyReturn");
        
        mv().visitInsn(RETURN);
    }

    @Override
    protected int maxNumberOfChildren() {
        return 1;
    }

}
