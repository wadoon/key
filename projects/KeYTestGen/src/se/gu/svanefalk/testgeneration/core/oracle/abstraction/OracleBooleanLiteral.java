package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

/**
 * Represents a literal of Boolean type
 * 
 * @author christopher
 * 
 */
public class OracleBooleanLiteral extends OracleBooleanExpression implements
        IOracleLiteral {

    private final String identifier;

    public OracleBooleanLiteral(final String identifier,
            final boolean truthValue) {
        super(truthValue);

        this.identifier = identifier;
    }

    /**
     * @return the identifier
     */
    @Override
    public String getIdentifier() {
        return this.identifier;
    }
}
