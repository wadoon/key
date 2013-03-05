package de.uka.ilkd.key.testgeneration.core.oracle;

public abstract class OracleBooleanExpression {

    private final boolean truthValue;

    public OracleBooleanExpression(boolean truthValue) {
        this.truthValue = truthValue;
    }

    public final boolean isTrue() {
        return truthValue;
    }
}
