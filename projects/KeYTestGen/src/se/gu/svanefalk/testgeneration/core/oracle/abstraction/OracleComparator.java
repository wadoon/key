package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

public class OracleComparator extends OracleExpression {

    public enum ComparatorType {

        GREATER_OR_EQUALS(">="), GREATER_THAN(">"), LESS_OR_EQUALS("<="), LESS_THAN(
                "<"), EQUALS("=="), NOT_EQUALS("!=");

        private final String identifier;

        private ComparatorType(final String identifier) {
            this.identifier = identifier;
        }

        @Override
        public String toString() {
            return this.identifier;
        }
    }

    private final ComparatorType comparator;
    private final OracleExpression firstOperand;
    private final OracleExpression secondOperand;

    public OracleComparator(final ComparatorType comparator,
            final OracleExpression firstOperand,
            final OracleExpression secondOperand) {

        super(OracleType.BOOLEAN);
        this.comparator = comparator;
        this.firstOperand = firstOperand;
        this.secondOperand = secondOperand;
    }

    public OracleExpression getFirstOperand() {

        return this.firstOperand;
    }

    public ComparatorType getOperation() {

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
