package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

/**
 * Represents a method invocation in an oracle. Note that this is not a
 * representation of the method itself - rather a single invocation of it:
 * nothing more is defined than the precise paramaters provided for this
 * particular invocation, the returntype of the method itself, as well as the
 * object instance which the invocation is being made from.
 * 
 * @author christopher
 * 
 */
public class OracleMethodInvocation extends OracleExpression {

    /**
     * The identifier for this method.
     */
    private final String identifier;

    /**
     * The parameters passed to this invocation of the method.
     */
    private final OracleExpression[] parameters;

    /**
     * The object which this method is being invoked from.
     */
    private final OracleLiteral parentObject;

    /**
     * Create a new method invocation.
     * 
     * @param returnType
     *            returntype of the method
     * @param identifier
     *            identifier of the method
     * @param parentObject
     *            object from which the method is being invoked
     * @param arguments
     *            arguments passed to the invocation
     */
    public OracleMethodInvocation(final OracleType returnType,
            final String identifier, final OracleLiteral parentObject,
            final OracleExpression[] arguments) {
        super(returnType);

        this.parentObject = parentObject;
        this.identifier = identifier;
        this.parameters = arguments;

    }

    /**
     * @return the identifier for the method.
     */
    public String getIdentifier() {
        return this.identifier;
    }

    /**
     * @return the parameters passed to the invocation.
     */
    public OracleExpression[] getParameters() {
        return this.parameters;
    }

    /**
     * @return the object from which the method is being invoked.
     */
    public OracleLiteral getParentObject() {
        return this.parentObject;
    }

    @Override
    public String toString() {
        final StringBuilder toPrint = new StringBuilder();

        toPrint.append(this.identifier);
        toPrint.append("(");
        for (int i = 0; i < this.parameters.length; i++) {
            toPrint.append(this.parameters[i]);
            if (i < (this.parameters.length - 1)) {
                toPrint.append(",");
            }
        }
        toPrint.append(")");

        return toPrint.toString();
    }
}