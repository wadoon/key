package se.gu.svanefalk.testgeneration.backend.junit.abstraction;

import se.gu.svanefalk.testgeneration.core.model.implementation.ModelInstance;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelVariable;

/**
 * Instances of this class represent standard Java variable declaration
 * assertions in a JUnit test class, of the following form:
 * 
 * <pre>
 * <code>{@literal <}type{@literal >} {@literal <}identifier{@literal >} = {@literal <}value{@literal >}
 * </pre>
 * 
 * <code>value</code> may be either a reference or primitive type. In the event
 * that it is a reference, it may be <code>null</code>.
 * 
 * @author christopher
 * 
 */
public class JUnitDeclarationStatement {

    /**
     * The identifier for the variable.
     */
    private final String identifier;

    /**
     * The type for the variable.
     */
    private final String type;

    /**
     * The instance pointed to.
     */
    private final String value;

    public JUnitDeclarationStatement(final ModelVariable variable) {
        type = variable.getType();
        identifier = variable.getIdentifier();

        final Object value = variable.getValue();
        if (value instanceof ModelInstance) {
            final ModelInstance instance = (ModelInstance) value;
            this.value = "new " + instance.getType() + "()";
        } else {
            this.value = value.toString();
        }
    }

    public JUnitDeclarationStatement(final String type,
            final String identifier, final String value) {
        super();
        this.type = type;
        this.identifier = identifier;
        this.value = value;
    }

    /**
     * @return the identifier
     */
    public String getIdentifier() {
        return identifier;
    }

    /**
     * @return the type
     */
    public String getType() {
        return type;
    }

    /**
     * @return the value
     */
    public String getValue() {
        return value;
    }
}