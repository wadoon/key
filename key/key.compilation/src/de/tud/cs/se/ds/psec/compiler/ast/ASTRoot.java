package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
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
     * @see TacletASTNode#TacletASTNode(MethodVisitor, ProgVarHelper,
     *      TranslationDefinitions, TacletApp)
     */
    public ASTRoot() {
        super(null, "", null, null, null, null, null);
    }

    @Override
    public void compile() {
        logger.trace("Compiling ASTRoot");

        compileFirstChild();
    }
}
