package de.tud.cs.se.ds.psec.parser.ast;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

/**
 * A container for {@link TranslationDefinition}s. You can obtain all
 * {@link TranslationDefinition}s for a given symbolic execution taclet name by
 * accessing {@link #getDefinitionsFor(String)}; with additional context
 * information, the method
 * {@link #getDefinitionFor(String, ApplicabilityCheckInput)} is able to return
 * the one matching definition (if any).
 *
 * @author Dominic Scheurer
 */
public class TranslationDefinitions {

    private HashMap<String, ArrayList<TranslationDefinition>> definitionsMap = new HashMap<>();

    public TranslationDefinitions(
            ArrayList<TranslationDefinition> definitions) {

        definitions.forEach(d -> d.getSymbExTacletReferences()
                .forEach(ref -> putDefinition(ref, d)));

    }

    /**
     * Returns all available translations for the given SE taclet name. From
     * those, at most one should be applicable for a specific situation.
     * 
     * @param symbExTacletName
     *            The symbolic execution taclet name designating the taclet to
     *            translate.
     * @return The list of matching {@link TranslationDefinition}s.
     */
    public ArrayList<TranslationDefinition> getDefinitionsFor(
            String symbExTacletName) {
        return definitionsMap.get(symbExTacletName);
    }

    /**
     * 
     * @param symbExTacletName
     *            The symbolic execution taclet name designating the taclet to
     *            translate.
     * @param context
     *            Context information for filtering the suitable
     *            {@link TranslationDefinition} from the list of available
     *            translations.
     * @return A suitable {@link TranslationDefinition} or null if there is
     *         none.
     */
    public TranslationDefinition getDefinitionFor(String symbExTacletName,
            ApplicabilityCheckInput context) {
        List<TranslationDefinition> candidates = getDefinitionsFor(
                symbExTacletName).stream()
                        .filter(defn -> defn.isApplicable(context))
                        .collect(Collectors.toList());

        if (!candidates.isEmpty()) {
            // There should be no case where more than one translation
            // is applicable. Otherwise, the rules would be badly designed.
            // Maybe we should print a warning, though...
            return candidates.get(0);
        }
        else {
            return null;
        }
    }

    private void putDefinition(String symbExTacletName,
            TranslationDefinition defn) {
        if (!definitionsMap.containsKey(symbExTacletName)) {
            definitionsMap.put(symbExTacletName, new ArrayList<>());
        }

        definitionsMap.get(symbExTacletName).add(defn);
    }

}
