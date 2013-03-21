package se.gu.svanefalk.testgeneration.core.oracle.abstraction.types;

public enum ReferenceComparatorType {
    EQUALS("=="), NOT_EQUALS("!=");

    private final String identifier;

    private ReferenceComparatorType(String identifier) {
        this.identifier = identifier;
    }

    public String toString() {
        return identifier;
    }
}
