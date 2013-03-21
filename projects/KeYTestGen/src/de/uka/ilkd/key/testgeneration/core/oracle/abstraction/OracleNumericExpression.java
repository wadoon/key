package de.uka.ilkd.key.testgeneration.core.oracle.abstraction;

import de.uka.ilkd.key.testgeneration.core.oracle.abstraction.types.NumericType;

public abstract class OracleNumericExpression {

    private final NumericType type;

    public OracleNumericExpression(NumericType type) {
        this.type = type;
    }

    private final NumericType getType() {
        return type;
    }
}

class PrimitiveNumericType {

    Boolean num;
}