package se.gu.svanefalk.testgeneration.core.oracle.abstraction.types;

public enum NumericComparatorType {
    EQUALS("=="), NOT_EQUALS("!="), GREATER_THAN(">"), GREATER_OR_EQUALS(">="), LESS_THAN(
            "<"), LESS_OR_EQUALS("<=");

    private final String identifier;

    private NumericComparatorType(String identifier) {
        this.identifier = identifier;
    }

    public String toString() {
        return identifier;
    }
}
