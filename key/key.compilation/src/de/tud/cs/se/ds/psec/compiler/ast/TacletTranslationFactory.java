package de.tud.cs.se.ds.psec.compiler.ast;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
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
     * List of taclets that are not meant to be translated, for instance because
     * they have no correspondent in bytecode or because they are followed by
     * decomposed simpler statements in the proof tree.<br>
     * 
     * <strong>NOTE:</strong> The entries in this list have to be alphabetically
     * sorted, since we perform a binary search on them.
     */
    private final static String[] UNTRANSLATED_TACLETS = {
    //@formatter:off
        "compound_addition_2",
        "compound_assignment_3_nonsimple",
        "compound_assignment_op_plus",
        "compound_binary_AND_2",
        "compound_greater_than_comparison_1",
        "compound_int_cast_expression",
        "compound_subtraction_1",
        "for_to_while",
        "ifElseUnfold",
        "ifUnfold",
        "loopComplexToSimple",
        "postdecrement",
        "postincrement_assignment",
        "preincrement_assignment",
        "remove_parentheses_right",
        "variableDeclaration",
        "variableDeclarationAssign",
        "widening_identity_cast_5",
     };
    //@formatter:on

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
            if (!isUntranslatedTaclet(tacletName)) {
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

    /**
     * Returns true iff the given taclet name corresponds to a taclet that
     * should not be translated into bytecode.
     *
     * @param tacletName
     *            Name of the taclet to check.
     * @return iff the given taclet name corresponds to a taclet that should not
     *         be translated into bytecode.
     */
    private static boolean isUntranslatedTaclet(String tacletName) {
        return Arrays.binarySearch(UNTRANSLATED_TACLETS, tacletName) > -1;
    }
}
