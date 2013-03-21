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

    public OracleBooleanLiteral(String identifier, boolean truthValue) {
        super(truthValue);

        this.identifier = identifier;
    }

    /**
     * @return the identifier
     */
    public String getIdentifier() {
        return identifier;
    }
}
