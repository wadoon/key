package de.uka.ilkd.key.testgeneration.core.oracle;

public class OracleComparator extends OracleBooleanExpression {

    public enum Comparator {
        EQUALS("=="), GREATER_THAN(">"), GREATER_OR_EQUALS(">="), LESS_THAN("<"), LESS_OR_EQUALS(
                "<=");

        private final String identifier;

        private Comparator(String identifier) {
            this.identifier = identifier;
        }

        public String toString() {
            return identifier;
        };
    }

    private final Comparator comparator;
    private final OracleNumericExpression firstOperand;
    private final OracleNumericExpression secondOperand;

    public OracleComparator(Comparator comparator,
            OracleNumericExpression firstOperand,
            OracleNumericExpression secondOperand, boolean truthValue) {
        super(truthValue);
        
        this.comparator = comparator;
        this.firstOperand = firstOperand;
        this.secondOperand = secondOperand;
    }

    public Comparator getOperation() {

        return comparator;
    }

    public OracleNumericExpression getFirstOperand() {

        return firstOperand;
    }

    public OracleNumericExpression getSecondOperand() {

        return secondOperand;
    }
}
