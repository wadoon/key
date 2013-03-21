package se.gu.svanefalk.testgeneration.core.oracle.abstraction.types;

/**
 * The possible primitve types for a numeric expression.
 */
public enum PrimitiveNumericType implements NumericType {
    INTEGER("int"), FLOAT("float"), BYTE("byte"), LONG("long"), DOUBLE("double");

    private final String identifier;

    private PrimitiveNumericType(String identifier) {
        this.identifier = identifier;
    }

    public String toString() {
        return identifier;
    }
}
