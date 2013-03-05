package de.uka.ilkd.key.testgeneration.core.oracle;

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