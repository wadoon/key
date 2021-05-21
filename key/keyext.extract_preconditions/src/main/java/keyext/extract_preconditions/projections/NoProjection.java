package keyext.extract_preconditions.projections;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * Projection which has no effect (i.e. leaves everything as is).
 */
public class NoProjection extends AbstractTermProjection{
    public NoProjection(Services servicesParam) {
        super(servicesParam);
    }

    @Override
    public Term projectTerm(Term inputTerm) {
        return inputTerm;
    }
}
