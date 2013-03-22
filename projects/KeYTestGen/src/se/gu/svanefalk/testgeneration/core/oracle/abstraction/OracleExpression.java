package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

public abstract class OracleExpression {

    private final OracleType type;

    public OracleExpression(OracleType type) {
        this.type = type;
    }

    /**
     * @return the type
     */
    public OracleType getType() {
        return type;
    }

    @Override
    public String toString() {

        return "OracleExpression, type: " + getType();
    }
}