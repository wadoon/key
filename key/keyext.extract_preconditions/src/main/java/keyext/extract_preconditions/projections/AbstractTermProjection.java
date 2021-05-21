package keyext.extract_preconditions.projections;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * Class which represents an abstract projection procedure of preconditions.
 * Applied to each precondition term separately.
 */
public abstract class AbstractTermProjection {

    protected Services services;

    public AbstractTermProjection(Services servicesParam) {
        this.services = servicesParam;
    }

    public abstract Term projectTerm(Term inputTerm);
}
