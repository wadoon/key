package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import se.gu.svanefalk.testgeneration.core.oracle.abstraction.types.NumericType;

public class OracleNumericLiteral extends OracleNumericExpression implements IOracleLiteral{

    private final String identifier;

    public OracleNumericLiteral(String identifier, NumericType type) {
        super(type);

        this.identifier = identifier;
    }

    /**
     * @return the identifier
     */
    public String getIdentifier() {
        return identifier;
    }
}
