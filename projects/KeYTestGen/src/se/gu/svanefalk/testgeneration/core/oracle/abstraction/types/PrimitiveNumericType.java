package se.gu.svanefalk.testgeneration.core.oracle.abstraction.types;

/**
 * The possible primitve types for a numeric expression.
 */
public enum PrimitiveNumericType implements NumericType {
    BYTE("byte"), DOUBLE("double"), FLOAT("float"), INTEGER("int"), LONG("long");

    private final String identifier;

    private PrimitiveNumericType(final String identifier) {
        this.identifier = identifier;
    }

    @Override
    public String toString() {
        return this.identifier;
    }
}
