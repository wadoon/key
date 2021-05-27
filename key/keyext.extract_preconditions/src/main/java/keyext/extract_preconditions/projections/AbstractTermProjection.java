package keyext.extract_preconditions.projections;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * Class which represents an abstract projection strategy of preconditions.
 * Applied to each precondition term separately.
 */
public abstract class AbstractTermProjection {

    protected Services services;

    /**
     * Abstract constructor for term projection strategies
     *
     * @param servicesParam The proof services object (necessary for term building etc.)
     */
    public AbstractTermProjection(Services servicesParam) {
        this.services = servicesParam;
    }

    /**
     * Method to project a term with the chosen strategy
     *
     * @param inputTerm Term to project
     * @return Term after projection
     */
    public abstract Term projectTerm(Term inputTerm);
}
