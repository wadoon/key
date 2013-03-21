package se.gu.svanefalk.testgeneration.core.oracle.abstraction.types;

/**
 * The possible reference (i.e. wrapper) types for a numeric expression.
 */
public enum WrapperNumericType implements NumericType {
    BYTE("Byte"), DOUBLE("Double"), FLOAT("Float"), INTEGER("Integer"), LONG(
            "Long");

    private final String identifier;

    private WrapperNumericType(final String identifier) {
        this.identifier = identifier;
    }

    @Override
    public String toString() {
        return this.identifier;
    }
}