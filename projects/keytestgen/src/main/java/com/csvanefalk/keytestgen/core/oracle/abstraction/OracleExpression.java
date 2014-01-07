package com.csvanefalk.keytestgen.core.oracle.abstraction;

/**
 * Represents a boolean expression in a constraint on the post-state of a
 * system. On a logical level, it corresponds (perhaps roughly) to a FOL
 * formula.
 * <p/>
 * This type is the basic type for all other elements present in a test Oracle,
 * apart from the Assertions and Constraints themselves, since these are
 * effectively container classes. The exception to this rule is the
 * {@link OracleConstraint} itself, which may still be bounded by a quantifier
 * and hence occur many times in a formula.
 *
 * @author christopher
 */
public abstract class OracleExpression {

    /**
     * The type of the expression.
     */
    private final OracleType type;

    /**
     * Constructs a new expression.
     *
     * @param type the type of the expression
     */
    public OracleExpression(final OracleType type) {
        this.type = type;
    }

    /**
     * @return the type
     */
    public OracleType getType() {
        return type;
    }

    @Override
    public String toString() {
        return "OracleExpression, type: " + getType();
    }
}