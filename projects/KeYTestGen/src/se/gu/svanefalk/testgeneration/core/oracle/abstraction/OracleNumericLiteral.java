package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import se.gu.svanefalk.testgeneration.core.oracle.abstraction.types.NumericType;

public class OracleNumericLiteral extends OracleNumericExpression implements
        IOracleLiteral {

    private final String identifier;

    public OracleNumericLiteral(final String identifier, final NumericType type) {
        super(type);

        this.identifier = identifier;
    }

    /**
     * @return the identifier
     */
    @Override
    public String getIdentifier() {
        return this.identifier;
    }
}
