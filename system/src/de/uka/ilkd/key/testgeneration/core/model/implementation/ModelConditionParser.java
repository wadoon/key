package de.uka.ilkd.key.testgeneration.core.model.implementation;

import de.uka.ilkd.key.logic.Term;

/**
 * Encapsulates functionality needed in order to parse the pre- and
 * postconditions of a proof, for the purpose of generating model data.
 * 
 * @author christopher
 */
public class ModelConditionParser {

    /**
     * Determines whether the condition contains external variables (as in
     * external to the method for which the condition applies.
     * 
     * @param condition
     * @return
     */
    private boolean hasExternalVariables(Term condition) {

        return true;
    }

}
