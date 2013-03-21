package se.gu.svanefalk.testgeneration.core.oracle.abstraction.types;

public enum NumericComparatorType {
    EQUALS("=="), GREATER_OR_EQUALS(">="), GREATER_THAN(">"), LESS_OR_EQUALS(
            "<="), LESS_THAN("<"), NOT_EQUALS("!=");

    private final String identifier;

    private NumericComparatorType(final String identifier) {
        this.identifier = identifier;
    }

    @Override
    public String toString() {
        return this.identifier;
    }
}
