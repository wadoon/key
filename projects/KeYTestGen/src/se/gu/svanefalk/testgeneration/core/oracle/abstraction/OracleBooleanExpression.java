package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

public abstract class OracleBooleanExpression {

    private final boolean truthValue;

    public OracleBooleanExpression(final boolean truthValue) {
        this.truthValue = truthValue;
    }

    public final boolean isTrue() {
        return this.truthValue;
    }
}
