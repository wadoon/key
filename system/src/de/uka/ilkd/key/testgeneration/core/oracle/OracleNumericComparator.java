package de.uka.ilkd.key.testgeneration.core.oracle;

public class OracleNumericComparator extends OracleBooleanExpression {

    public enum NumericComparatorType {
        EQUALS("=="), NOT_EQUALS("!="), GREATER_THAN(">"), GREATER_OR_EQUALS(
                ">="), LESS_THAN("<"), LESS_OR_EQUALS("<=");

        private final String identifier;

        private NumericComparatorType(String identifier) {
            this.identifier = identifier;
        }

        public String toString() {
            return identifier;
        };
    }

    private final NumericComparatorType comparator;
    private final OracleNumericExpression firstOperand;
    private final Number secondOperand;

    public OracleNumericComparator(NumericComparatorType comparator,
            OracleNumericExpression firstOperand, Number secondOperand,
            boolean truthValue) {
        super(truthValue);

        this.comparator = comparator;
        this.firstOperand = firstOperand;
        this.secondOperand = secondOperand;
    }

    public NumericComparatorType getOperation() {

        return comparator;
    }

    public OracleNumericExpression getFirstOperand() {

        return firstOperand;
    }

    public Number getSecondOperand() {

        return secondOperand;
    }
}
