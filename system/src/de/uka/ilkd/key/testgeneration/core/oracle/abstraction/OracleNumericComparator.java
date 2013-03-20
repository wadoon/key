package de.uka.ilkd.key.testgeneration.core.oracle.abstraction;

import de.uka.ilkd.key.testgeneration.core.oracle.abstraction.types.NumericComparatorType;

public class OracleNumericComparator extends OracleBooleanExpression {

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
