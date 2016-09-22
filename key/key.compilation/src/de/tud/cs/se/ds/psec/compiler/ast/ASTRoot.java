package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * The root of the {@link Taclet} AST.
 *
 * @author Dominic Scheurer
 */
class ASTRoot extends TacletASTNode {
    private static final Logger logger = LogManager.getFormatterLogger();
    
    /**
     * @see TacletASTNode#TacletASTNode(MethodVisitor, ProgVarHelper, TacletApp)
     */
    public ASTRoot(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        logger.trace("Compiling ASTRoot");
        
        compileFirstChild();
    }

    @Override
    protected int maxNumberOfChildren() {
        return 1;
    }
}
