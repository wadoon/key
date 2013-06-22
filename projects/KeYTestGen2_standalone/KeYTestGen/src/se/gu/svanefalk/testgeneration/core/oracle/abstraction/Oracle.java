package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

/**
 * Represents a test case oracle - that is, a set of constraints on post-state
 * of a program following the execution of a test case.
 * 
 * @author christopher
 */
public class Oracle {

    /**
     * The set of constraints on the poststate represented by this Oracle.
     */
    private final OracleConstraint constraints;

    /**
     * The exception expected to be thrown by the method under test, if any.
     */
    private final OracleType expectedException;

    /**
     * Creates a new Oracle
     * 
     * @param constraints
     *            the constraints on the poststate
     * @param expectedException
     *            the expected exception
     */
    public Oracle(final OracleConstraint constraints,
            final OracleType expectedException) {
        super();
        this.constraints = constraints;
        this.expectedException = expectedException;
    }

    /**
     * @return the constraints
     */
    public OracleConstraint getConstraints() {
        return constraints;
    }

    /**
     * @return the expectedException
     */
    public OracleType getExpectedException() {
        return expectedException;
    }
}