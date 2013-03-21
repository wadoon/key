package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

public abstract class OracleReferenceExpression {

    private final String type;

    public OracleReferenceExpression(String type) {
        this.type = type;
    }

    private final String getType() {
        return type;
    }
}
