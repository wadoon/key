package de.uka.ilkd.key.testgeneration.core.oracle;

import de.uka.ilkd.key.testgeneration.core.oracle.types.ReferenceComparatorType;

public class OracleReferenceComparator extends OracleBooleanExpression {

    private final ReferenceComparatorType comparator;
    private final OracleReferenceExpression firstOperand;
    private final OracleReferenceExpression secondOperand;

    public OracleReferenceComparator(ReferenceComparatorType comparator,
            OracleReferenceExpression firstOperand,
            OracleReferenceExpression secondOperand, boolean truthValue) {
        super(truthValue);

        this.comparator = comparator;
        this.firstOperand = firstOperand;
        this.secondOperand = secondOperand;
    }

    public ReferenceComparatorType getOperation() {

        return comparator;
    }

    public OracleReferenceExpression getFirstOperand() {

        return firstOperand;
    }

    public OracleReferenceExpression getSecondOperand() {

        return secondOperand;
    }
}
