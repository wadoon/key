package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import se.gu.svanefalk.testgeneration.core.oracle.abstraction.types.NumericComparatorType;

public class OracleNumericComparator extends OracleBooleanExpression {

    private final NumericComparatorType comparator;
    private final OracleNumericExpression firstOperand;
    private final Number secondOperand;

    public OracleNumericComparator(final NumericComparatorType comparator,
            final OracleNumericExpression firstOperand,
            final Number secondOperand, final boolean truthValue) {
        super(truthValue);

        this.comparator = comparator;
        this.firstOperand = firstOperand;
        this.secondOperand = secondOperand;
    }

    public OracleNumericExpression getFirstOperand() {

        return this.firstOperand;
    }

    public NumericComparatorType getOperation() {

        return this.comparator;
    }

    public Number getSecondOperand() {

        return this.secondOperand;
    }
}
