package de.tud.cs.se.ds.psec.compiler.taclet_translation;

import java.util.Arrays;
import java.util.HashMap;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Factory class for creating taclet translations.
 *
 * @author Dominic Scheurer
 */
public class TacletTranslationFactory {
    private static final Logger logger = LogManager.getFormatterLogger();

    private MethodVisitor mv;
    private ProgVarHelper pvHelper;
    private HashMap<String, TacletTranslation> translations = new HashMap<>();
    private final DummyTranslation DUMMY_TRANSLATION;

    /**
     * List of taclets that are not meant to be translated, for instance because
     * they have no correspondant in bytecode or because they are followed by
     * decomposed simpler statements in the proof tree.<br>
     * 
     * <strong>NOTE:</strong> The entries in this list have to be alphabetically
     * sorted, since we perform a binary search on them.
     */
    private final static String[] UNTRANSLATED_TACLETS = {
            "compound_addition_2",
            "compound_assignment_op_plus",
            "compound_greater_than_comparison_1",
            "compound_int_cast_expression",
            "ifUnfold",
            "postincrement_assignment",
            "remove_parentheses_right",
            "variableDeclaration",
            "variableDeclarationAssign",
            "widening_identity_cast_5",
    };

    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public TacletTranslationFactory(MethodVisitor mv, ProgVarHelper pvHelper) {
        this.mv = mv;
        this.pvHelper = pvHelper;
        this.DUMMY_TRANSLATION = new DummyTranslation(mv, pvHelper);
    }

    /**
     * Returns a {@link TacletTranslation} class for the given
     * {@link TacletApp}. May return a {@link DummyTranslation} if no suitable
     * translation is found.
     *
     * @param app
     *            The {@link TacletApp} for which to create a translation
     *            object.
     * @return A {@link TacletTranslation} for the given {@link TacletApp} or a
     *         {@link DummyTranslation} if there is no suitable such
     *         {@link TacletTranslation}.
     */
    public TacletTranslation getTranslationForTacletApp(TacletApp app) {
        String tacletName = app.taclet().name().toString();
        logger.trace("Translating taclet %s", tacletName);

        if (translations.containsKey(tacletName)) {
            return translations.get(tacletName);
        }

        TacletTranslation result = DUMMY_TRANSLATION;

        switch (tacletName) {
        // Assignments
        case "assignment":
            result = new Assignment(mv, pvHelper);
            break;
        case "assignmentSubtractionInt":
            result = new AssignmentSubtractionInt(mv, pvHelper);
            break;
        // Return Statements
        // TODO: Support also returnUnfold and STOP EXECUTING afterward.
        case "methodCallReturn":
            result = new MethodCallReturn(mv, pvHelper);
            break;
        case "methodCallEmptyReturn":
            result = new MethodCallEmptyReturn(mv, pvHelper);
            break;
        // Arithmetic operations
        case "assignmentAdditionInt":
            result = new AssignmentAdditionInt(mv, pvHelper);
            break;
        case "greater_than_comparison_simple":
            result = new GreaterThanComparisonSimple(mv, pvHelper);
            break;
        default:
            if (!isUntranslatedTaclet(tacletName)) {
                logger.error("Don't know a translation of the following taclet app: %s",
                        app.rule().name());
            } else {
                logger.debug("Ignoring taclet %s", app.rule().name());
            }
        }

        if (result != null) {
            translations.put(tacletName, result);
        }

        return result;
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

    /**
     * A translation that does not do anything; in the preliminary state of
     * Alfred, this is partly used for taclets not yet supported; however, it
     * may also be used for taclets that are not meant to be translated, like
     * complex expressions or variable initializations.
     *
     * @author Dominic Scheurer
     */
    static class DummyTranslation extends TacletTranslation {
        /**
         * TODO
         * 
         * @param mv
         * @param pvHelper
         */
        public DummyTranslation(MethodVisitor mv, ProgVarHelper pvHelper) {
            super(mv, pvHelper);
        }

        @Override
        public void compile(TacletApp app) {
            // Dummy translation does not do anything
        }
    }
}
