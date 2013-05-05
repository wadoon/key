package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

/**
 * Represents, loosely, a literal in a FOL formula, which may be either a
 * variable or a constant.
 * 
 * @author christopher
 */
public class OracleLiteral extends OracleExpression {

    /**
     * The identifier for this literal.
     */
    private final String identifier;

    /**
     * Constructs a new literal.
     * 
     * @param type
     *            type of the literal
     * @param identifier
     *            identifier for the literal
     */
    public OracleLiteral(final OracleType type, final String identifier) {
        super(type);
        this.identifier = identifier;
    }

    /**
     * @return the identifier
     */
    public String getIdentifier() {
        return identifier;
    }

    @Override
    public String toString() {
        return identifier + ":" + getType();
    }
}