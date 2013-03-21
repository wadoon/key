package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

public class OracleQuantifier extends OracleBooleanExpression {

    private final IOracleLiteral conditionVariable;
    private final OracleBooleanExpression conditionExpression;

    public OracleQuantifier(IOracleLiteral conditionVariable,
            OracleBooleanExpression conditionExpression, boolean truthValue) {
        super(truthValue);

        this.conditionVariable = conditionVariable;
        this.conditionExpression = conditionExpression;
    }
}