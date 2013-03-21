package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

public class OracleQuantifier extends OracleBooleanExpression {

    public OracleQuantifier(final IOracleLiteral conditionVariable,
            final OracleBooleanExpression conditionExpression,
            final boolean truthValue) {
        super(truthValue);
    }
}