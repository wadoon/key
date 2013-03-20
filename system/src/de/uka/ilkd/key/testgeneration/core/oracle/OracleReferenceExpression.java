package de.uka.ilkd.key.testgeneration.core.oracle;

public abstract class OracleReferenceExpression {

    private final String type;

    public OracleReferenceExpression(String type) {
        this.type = type;
    }

    private final String getType() {
        return type;
    }
}
