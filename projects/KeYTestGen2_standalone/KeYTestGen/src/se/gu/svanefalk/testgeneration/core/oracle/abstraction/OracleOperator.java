package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

/**
 * Represents an operator as part of an oracle. Conceptually, it is different
 * from an {@link OracleComparator} only in the sense that it can have a
 * different type than just boolean, and is hence used to represent, for
 * instance, arithmetic operations.
 * <p>
 * Like {@link OracleComparator} instances, operators are not type safe, but
 * rely on KeY to make sure that the underlying formulas are already in such a
 * state.
 * 
 * @author christopher
 * 
 */
public class OracleOperator extends OracleExpression {

    /**
     * The type of the operators in oracles.
     * 
     * @author christopher
     */
    public enum OperatorType {

        /**
         * The addition operator.
         */
        ADDITION("+"),

        /**
         * The division operator.
         */
        DIVISION("/"),

        /**
         * The modulo operator.
         */
        MODULO("%"),

        /**
         * The multiplication operator.
         */
        MULTIPLICATION("*"),

        /**
         * The subtraction operator.
         */
        SUBTRACTION("-");

        /**
         * The identifier for this operator type.
         */
        private final String identifier;

        /**
         * Constructs a new operator type.
         * 
         * @param identifier
         *            the identifier for the operator
         */
        private OperatorType(final String identifier) {
            this.identifier = identifier;
        }

        @Override
        public String toString() {
            return identifier;
        }
    }

    /**
     * The first operand of this operator.
     */
    private final OracleExpression firstOperand;

    /**
     * The type of this operator.
     */
    private final OperatorType operatorType;

    /**
     * The second operand of this operator.
     */
    private final OracleExpression secondOperand;

    /**
     * Constructs a new operator.
     * 
     * @param comparatorType
     *            the type of the operator
     * @param firstOperand
     *            the first operand of the operator
     * @param secondOperand
     *            the second operand of the operator
     * @param type
     *            the resulting type of the operation itself
     */
    public OracleOperator(final OperatorType comparatorType,
            final OracleExpression firstOperand,
            final OracleExpression secondOperand, final OracleType type) {
        super(type);

        operatorType = comparatorType;
        this.firstOperand = firstOperand;
        this.secondOperand = secondOperand;
    }

    /**
     * @return the first operand of this operator.
     */
    public OracleExpression getFirstOperand() {

        return firstOperand;
    }

    /**
     * @return the type of this operator
     */
    public OperatorType getOperation() {

        return operatorType;
    }

    /**
     * @return the second operand of this operator.
     */
    public OracleExpression getSecondOperand() {

        return secondOperand;
    }

    @Override
    public String toString() {
        return firstOperand.toString() + " " + operatorType.toString() + " "
                + secondOperand.toString();
    }
}