package com.csvanefalk.keytestgen.core.oracle.abstraction;

import com.csvanefalk.keytestgen.StringConstants;

/**
 * Represents a quantifier in an oracle expression, semantically equivalent to
 * the same construct in a FOL formula.
 *
 * @author christopher
 */
public class OracleQuantifier extends OracleExpression {

    /**
     * The possible types of quantifiers.
     *
     * @author christopher
     */
    public enum QuantifierType {

        /**
         * The exists quantifier.
         */
        EXISTS(StringConstants.EXISTS),

        /**
         * The for-all quantifier.
         */
        FORALL(StringConstants.FORALL);

        /**
         * Identifier for this quantifier type.
         */
        private final String identifier;

        private QuantifierType(final String identifier) {
            this.identifier = identifier;
        }

        @Override
        public String toString() {
            return identifier;
        }
    }

    /**
     * The expression bound to this quantifier.
     */
    private final OracleConstraint boundExpression;

    /**
     * The quantifiable variable of this quantifier, i.e. the variable over
     * which the quantification takes place.
     */
    private final OracleLiteral quantifiableVariable;

    /**
     * The type of this quantifier.
     */
    private final QuantifierType quantifierTtype;

    /**
     * Constructs a new quantifier.
     *
     * @param type                 the type of this quantifier
     * @param quantifiableVariable the quantified variable of this quantifier
     * @param boundExpression      the expression bound to this quantifier
     */
    public OracleQuantifier(final QuantifierType type,
                            final OracleLiteral quantifiableVariable,
                            final OracleConstraint boundExpression) {
        super(OracleType.BOOLEAN);

        this.boundExpression = boundExpression;
        this.quantifiableVariable = quantifiableVariable;
        quantifierTtype = type;
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

    /**
     * @return the {@link QuantifierType} of this quantifier.
     */
    public QuantifierType getQuantifierType() {
        return quantifierTtype;
    }

    @Override
    public String toString() {
        return getQuantifierType() + "(" + getQuantifiableVariable() + ")" + " {" + getBoundExpression() + " } ";
    }
}