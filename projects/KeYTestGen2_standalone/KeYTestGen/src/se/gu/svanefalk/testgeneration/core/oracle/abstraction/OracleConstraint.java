package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import java.util.Iterator;
import java.util.Set;

/**
 * An {@link OracleConstraint} is a set of assertions which must hold for the
 * poststate of the system under test, in order for the testcase to be
 * considered a success.
 * <p>
 * On a logical level, it is semantically equivalent to a set of formulas joined
 * by conjunction. These sub-formulas must in turn by joined only by
 * disjunctions (i.e. the entire formula represented by this class must be in
 * Conjunctive Normal Form). In our abstraction, such sub-formulas ar explicitly
 * represented by {@link OracleAssertion} instanes.
 * 
 * @author christopher
 * 
 */
public class OracleConstraint {

    /**
     * The assertions on the poststate represented by this constraint.
     */
    private final Set<OracleAssertion> assertions;

    /**
     * Sets up a constraint.
     * 
     * @param assertions
     *            the assertions associated with this constraint.
     */
    public OracleConstraint(final Set<OracleAssertion> assertions) {
        this.assertions = assertions;
    }

    /**
     * @return the assertions present in this constraint.
     */
    public Set<OracleAssertion> getAssertions() {
        return assertions;
    }

    @Override
    public String toString() {

        final StringBuilder toPrint = new StringBuilder();
        final Iterator<OracleAssertion> iterator = assertions.iterator();
        while (iterator.hasNext()) {
            toPrint.append("(" + iterator.next() + ")");
            if (iterator.hasNext()) {
                toPrint.append(" && ");
            }
        }
        return toPrint.toString();
    }
}