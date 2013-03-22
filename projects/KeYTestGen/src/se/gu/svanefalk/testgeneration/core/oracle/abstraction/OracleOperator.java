package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

public class OracleOperator extends OracleExpression {

    public enum OperatorType {

        ADDITION("+"), SUBTRACTION("-"), MULTIPLICATION("*"), DIVISION("/"), MODULO(
                "%");

        private final String identifier;

        private OperatorType(final String identifier) {
            this.identifier = identifier;
        }

        @Override
        public String toString() {
            return this.identifier;
        }
    }

    private final OperatorType comparator;
    private final OracleExpression firstOperand;
    private final OracleExpression secondOperand;

    public OracleOperator(final OperatorType comparator,
            final OracleExpression firstOperand,
            final OracleExpression secondOperand, OracleType type) {
        super(type);

        this.comparator = comparator;
        this.firstOperand = firstOperand;
        this.secondOperand = secondOperand;
    }

    public OracleExpression getFirstOperand() {

        return this.firstOperand;
    }

    public OperatorType getOperation() {

        return this.comparator;
    }

    public OracleExpression getSecondOperand() {

        return this.secondOperand;
    }

    @Override
    public String toString() {

        return firstOperand.toString() + " " + comparator.toString() + " "
                + secondOperand.toString();
    }
}