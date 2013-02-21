package de.uka.ilkd.key.testgeneration.backend.junit.abstraction;

import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelInstance;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelVariable;

/**
 * Instances of this class represent standard Java variable declaration
 * statements in a JUnit test class, of the following form:
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
     * The type for the variable.
     */
    private final String type;

    /**
     * The identifier for the variable.
     */
    private final String identifier;

    /**
     * The instance pointed to.
     */
    private final String value;

    public JUnitDeclarationStatement(String type, String identifier,
            String value) {
        super();
        this.type = type;
        this.identifier = identifier;
        this.value = value;
    }

    public JUnitDeclarationStatement(ModelVariable variable) {
        this.type = variable.getType();
        this.identifier = variable.getIdentifier();

        Object value = variable.getValue();
        if (value instanceof ModelInstance) {
            ModelInstance instance = (ModelInstance) value;
            this.value = "new " + instance.getType() + "()";
        } else {
            this.value = value.toString();
        }
    }

    /**
     * @return the type
     */
    public String getType() {
        return type;
    }

    /**
     * @return the identifier
     */
    public String getIdentifier() {
        return identifier;
    }

    /**
     * @return the value
     */
    public String getValue() {
        return value;
    }
}