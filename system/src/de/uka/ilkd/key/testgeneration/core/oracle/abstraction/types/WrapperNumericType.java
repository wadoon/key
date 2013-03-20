package de.uka.ilkd.key.testgeneration.core.oracle.abstraction.types;

/**
 * The possible reference (i.e. wrapper) types for a numeric expression.
 */
public enum WrapperNumericType implements NumericType {
    INTEGER("Integer"), FLOAT("Float"), BYTE("Byte"), LONG("Long"), DOUBLE(
            "Double");

    private final String identifier;

    private WrapperNumericType(String identifier) {
        this.identifier = identifier;
    }

    public String toString() {
        return identifier;
    }
}