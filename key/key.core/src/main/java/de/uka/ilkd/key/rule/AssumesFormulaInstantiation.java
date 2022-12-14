package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;


/*
 * This interface represents objects representing an instantiation of one formula of the assumes-sequent
 * of a taclet.
 */

public interface AssumesFormulaInstantiation {

    /**
     * @return the cf this is pointing to
     */
    SequentFormula getConstrainedFormula();

    String toString(Services services);
}
