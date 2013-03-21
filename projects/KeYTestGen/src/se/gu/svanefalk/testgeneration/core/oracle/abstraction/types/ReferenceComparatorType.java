package se.gu.svanefalk.testgeneration.core.oracle.abstraction.types;

public enum ReferenceComparatorType {
    EQUALS("=="), NOT_EQUALS("!=");

    private final String identifier;

    private ReferenceComparatorType(final String identifier) {
        this.identifier = identifier;
    }

    @Override
    public String toString() {
        return this.identifier;
    }
}
