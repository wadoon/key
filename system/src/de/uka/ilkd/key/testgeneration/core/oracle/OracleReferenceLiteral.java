package de.uka.ilkd.key.testgeneration.core.oracle;

public class OracleReferenceLiteral extends OracleReferenceExpression {

    private final String identifier;

    public OracleReferenceLiteral(String type, String identifier) {
        super(type);

        this.identifier = identifier;
    }
}
