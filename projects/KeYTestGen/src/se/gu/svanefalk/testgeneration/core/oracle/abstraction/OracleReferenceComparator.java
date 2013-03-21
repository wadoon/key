package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import se.gu.svanefalk.testgeneration.core.oracle.abstraction.types.ReferenceComparatorType;

public class OracleReferenceComparator extends OracleBooleanExpression {

    private final ReferenceComparatorType comparator;
    private final OracleReferenceExpression firstOperand;
    private final OracleReferenceExpression secondOperand;

    public OracleReferenceComparator(final ReferenceComparatorType comparator,
            final OracleReferenceExpression firstOperand,
            final OracleReferenceExpression secondOperand,
            final boolean truthValue) {
        super(truthValue);

        this.comparator = comparator;
        this.firstOperand = firstOperand;
        this.secondOperand = secondOperand;
    }

    public OracleReferenceExpression getFirstOperand() {

        return this.firstOperand;
    }

    public ReferenceComparatorType getOperation() {

        return this.comparator;
    }

    public OracleReferenceExpression getSecondOperand() {

        return this.secondOperand;
    }
}
