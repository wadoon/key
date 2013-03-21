package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import se.gu.svanefalk.testgeneration.core.oracle.abstraction.types.NumericType;

public abstract class OracleNumericExpression {

    private final NumericType type;

    public OracleNumericExpression(final NumericType type) {
        this.type = type;
    }
}

class PrimitiveNumericType {

    Boolean num;
}