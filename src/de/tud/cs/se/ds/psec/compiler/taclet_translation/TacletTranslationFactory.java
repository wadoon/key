package de.tud.cs.se.ds.psec.compiler.taclet_translation;

import java.util.HashMap;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Factory class for creating taclet translations.
 *
 * @author Dominic Scheurer
 */
public class TacletTranslationFactory {
    private MethodVisitor mv;
    private ProgVarHelper pvHelper;
    private HashMap<String, TacletTranslation> translations = new HashMap<>();
    private final DummyTranslation DUMMY_TRANSLATION;

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
        default:
            System.out.println(
                    "[INFO] Did not translate the following taclet app: "
                            + app.rule().name());
        }

        if (result != null) {
            translations.put(tacletName, result);
        }

        return result;
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
