package de.tud.cs.se.ds.psec.compiler.ast;

import java.util.List;
import java.util.Optional;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Factory class for creating {@link TacletASTNode}s in course of the execution
 * of a particular method. Main methods are:
 * 
 * <ul>
 * <li>{@link #getTranslationForTacletApp(TacletApp)}<br>
 * returns a {@link TacletASTNode} for the given {@link TacletApp}.</li>
 * <li>{@link #getASTRootNode()}<br>
 * returns a root node for a taclet AST.</li>
 * </ul>
 *
 * @author Dominic Scheurer
 */
public class TacletTranslationFactory {
    private static final Logger logger = LogManager.getFormatterLogger();

    private MethodVisitor mv;
    private TranslationDefinitions definitions = null;
    private ProgVarHelper pvHelper;

    /**
     * Creates a new {@link TacletTranslationFactory}.
     * 
     * @param mv
     *            The {@link MethodVisitor} used in compilation of the
     *            corresponding method.
     * @param pvHelper
     *            The {@link ProgVarHelper} for obtaining indices for program
     *            variables.
     * @param definitions
     *            TODO
     */
    public TacletTranslationFactory(MethodVisitor mv, ProgVarHelper pvHelper,
            TranslationDefinitions definitions) {
        this.mv = mv;
        this.pvHelper = pvHelper;
        this.definitions = definitions;
    }

    /**
     * Creates a root node for the AST.
     *
     * @return A root node for the AST.
     */
    public TacletASTNode getASTRootNode() {
        return new ASTRoot();
    }

    /**
     * Returns an {@link Optional} comprising a {@link TacletASTNode} for the
     * given {@link TacletApp}.
     *
     * @param app
     *            The {@link TacletApp} for which to create a translation
     *            object.
     * @return An {@link Optional} with a {@link TacletASTNode} for the given
     *         {@link TacletApp} or an empty {@link Optional} if there is no
     *         suitable such {@link TacletASTNode}.
     */
    public Optional<TacletASTNode> getTranslationForTacletApp(TacletApp app) {
        String tacletName = app.taclet().name().toString();
        logger.trace("Translating taclet %s", tacletName);

        TacletASTNode result = null;

        List<TranslationDefinition> candidates = definitions
                .getDefinitionsFor(tacletName);

        if (candidates != null) {
            result = new TacletASTNode(tacletName, candidates, mv, pvHelper,
                    app);
        }
        else {
            if (!isSimplificationSETaclet(app.taclet())) {
                logger.error(
                        "Don't know a translation of the following taclet app: %s",
                        app.rule().name());
                System.exit(1);
            }
            else {
                logger.debug("Ignoring taclet %s", app.rule().name());
            }
        }

        return result == null ? Optional.empty() : Optional.of(result);
    }

    /**
     * Checks whether a symbolic execution taclet is only simplifying the Java
     * expression and therefore may be ignored in compilation (there will be
     * further {@link TacletApp}s generated from those ignored
     * {@link TacletApp}s that are actually compiled).
     * <p>
     * 
     * We ignore a {@link Taclet} iff:
     * <ul>
     * <li>It has a <code>\replacewith</code> part generating exactly one new
     * sequent, <strong>and</strong></li>
     * <li>It does not change the symbolic state, i.e. the top level
     * {@link Operator} of the <code>\replacewith</code> part is
     * <strong>not</strong> an {@link UpdateApplication}.</li>
     * </ul>
     * 
     * @param taclet
     *            The {@link Taclet} to check.
     * @return true iff this {@link Taclet} may be ignored in compilation.
     */
    private static boolean isSimplificationSETaclet(Taclet taclet) {
        if (taclet.goalTemplates().size() != 1) {
            return false;
        }

        Operator replTermTopLevelOp = ((Term) taclet.goalTemplates().head()
                .replaceWithExpressionAsObject()).op();

        return !(replTermTopLevelOp instanceof UpdateApplication);
    }

    /**
     * Tries to return a {@link TacletASTNode} for the given SE taclet name. The
     * corresponding SE taclet may not depend on the instantiation of schema
     * variables!
     *
     * @param app
     *            The name of the {@link Taclet} to return a translation for.
     * @return An {@link Optional} with a {@link TacletASTNode} for the given
     *         {@link TacletApp} or an empty {@link Optional} if there is no
     *         suitable such {@link TacletASTNode}.
     */
    public Optional<TacletASTNode> getTranslationForTacletWithoutArgs(
            String tacletName) {
        logger.trace("Translating taclet %s", tacletName);

        TacletASTNode result = new TacletASTNode(tacletName,
                definitions.getDefinitionsFor(tacletName), mv, pvHelper, null);

        return result == null ? Optional.empty() : Optional.of(result);
    }
}
