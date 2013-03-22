package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

public class OracleLiteral extends OracleExpression {

    private final String identifier;

    public OracleLiteral(OracleType type, String identifier) {
        super(type);
        this.identifier = identifier;
    }

    /**
     * @return the identifier
     */
    public String getIdentifier() {
        return identifier;
    }

    @Override
    public String toString() {
        return identifier + ":" + getType();
    }
}