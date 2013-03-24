package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import se.gu.svanefalk.testgeneration.StringConstants;

/**
 * Represents a quantifier in an oracle expression, semantically equivalent to
 * the same construct in a FOL formula.
 * 
 * @author christopher
 * 
 */
public class OracleQuantifier extends OracleExpression {

    /**
     * The possible types of quantifiers.
     * 
     * @author christopher
     */
    public enum QuantifierType {

        /**
         * The for-all quantifier.
         */
        FORALL(StringConstants.FORALL),

        /**
         * The exists quantifier.
         */
        EXISTS(StringConstants.EXISTS);

        /**
         * Identifier for this quantifier type.
         */
        private final String identifier;

        private QuantifierType(final String identifier) {
            this.identifier = identifier;
        }

        @Override
        public String toString() {
            return this.identifier;
        }
    }

    /**
     * The type of this quantifier.
     */
    private final QuantifierType quantifierTtype;

    /**
     * The quantifiable variable of this quantifier, i.e. the variable over
     * which the quantification takes place.
     */
    private final OracleLiteral quantifiableVariable;

    /**
     * The expression bound to this quantifier.
     */
    private final OracleConstraint boundExpression;

    /**
     * Constructs a new quantifier.
     * 
     * @param type
     *            the type of this quantifier
     * @param quantifiableVariable
     *            the quantified variable of this quantifier
     * @param boundExpression
     *            the expression bound to this quantifier
     */
    public OracleQuantifier(final QuantifierType type,
            OracleLiteral quantifiableVariable, OracleConstraint boundExpression) {
        super(OracleType.BOOLEAN);

        this.boundExpression = boundExpression;
        this.quantifiableVariable = quantifiableVariable;
        this.quantifierTtype = type;
    }

    /**
     * @return the {@link QuantifierType} of this quantifier.
     */
    public QuantifierType getQuantifierType() {
        return quantifierTtype;
    }

    /**
     * @return the expression bound to this quantifier.
     */
    public OracleConstraint getBoundExpression() {
        return boundExpression;
    }

    /**
     * @return the variable quantified over by this quantifier.
     */
    public OracleLiteral getQuantifiableVariable() {
        return quantifiableVariable;
    }

    @Override
    public String toString() {
        return getQuantifierType() + "(" + getQuantifiableVariable() + ")"
                + " {" + getBoundExpression() + " } ";
    }
}