package se.gu.svanefalk.testgeneration.core.model.implementation;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Instances of this class represent Java program variables during runtime. It's
 * main function is to encapsulate a corresponding instance of
 * {@link ProgramVariable}, which will contain rather complete information about
 * the variable itself. However, it adds an additional layer of runtime
 * information, showing exactly which concrete object on the heap this variable
 * points to.
 * <p>
 * Instances of this class can represent either an object reference or primitive
 * type reference.
 * <ul>
 * <li>If it represents an object reference, its bound value will be a
 * {@link ModelInstance}, representing the heap object this variable is pointing
 * to. This value defaults null if no reference is given.</li>
 * <li>If it represents a primitive reference, then its value be one of the
 * primitive wrapper classes supported by KeY ({@link Integer}, {@link Boolean},
 * {@link Long}, {@link Byte} or {@link Character}). It cannot be null in this
 * case.</li>
 * </ul>
 * 
 * @author christopher
 */
public class ModelVariable {

    /**
     * Factory method for creating a {@link ModelVariable} instance.
     * 
     * @param programVariable
     *            the {@link IProgramVariable} instance which will be wrapped by
     *            the created instance.
     * @param identifier
     *            a unique identifier for the variable.
     * @return the created instance.
     */
    public static ModelVariable constructModelVariable(
            final IProgramVariable programVariable, final String identifier) {

        return new ModelVariable(programVariable, identifier);
    }

    public static boolean isValidValueType(final Object object) {

        return (object == null || object.getClass() == ModelInstance.class)
                || (object.getClass() == Integer.class)
                || (object.getClass() == Byte.class)
                || (object.getClass() == Long.class)
                || (object.getClass() == Boolean.class);
    }

    /**
     * The value bound to this object. Primitive types are represented by their
     * wrapper types ( {@link Integer}, {@link Boolean} etc).
     */
    private Object boundValue;

    /**
     * Represents a unique identifier for this variable, denoting its relative
     * point of declaration in the program, in the form
     * self_dot_someField_dot_someOtherField_dot_thisvariable. Since no two
     * variables can have the same declaration space, this is also used to
     * uniquely distinguish this variable as a {@link IHeapObject}.
     */
    private final String identifier;

    /**
     * This flag indicates whether or not this variable is declared in the
     * parameter list for a method.
     */
    private boolean isParameter = false;

    /**
     * The instance of {@link ModelInstance} in which this particular instance
     * of {@link ModelVariable} has been initialized.
     */
    private ModelInstance parentModelInstance;

    /**
     * The wrapped {@link ProgramVariable} instance.
     */
    private final IProgramVariable variable;

    private ModelVariable(final IProgramVariable programVariable,
            final String identifier) {

        variable = programVariable;
        this.identifier = identifier;
    }

    /**
     * Since we are working with unique Java assertions, two
     * {@link ModelVariable} instances are equal iff. their paths are identical.
     */
    @Override
    public boolean equals(final Object obj) {

        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ModelVariable other = (ModelVariable) obj;
        return identifier.equals(other.identifier);
    }

    /**
     * A variable is uniquely identified by its identifier.
     */
    public String getIdentifier() {

        return identifier;
    }

    /**
     * Returns the {@link ModelInstance} of which this variable is a field
     * 
     * @return
     */
    public ModelInstance getParentModelInstance() {

        return parentModelInstance;
    }

    /**
     * Returns a String representation of the {@link KeYJavaType} of this
     * variable.
     */
    public String getTypeName() {

        return variable.getKeYJavaType().getName();
    }

    /**
     * Returns the value of the variable. Will have to be explicitly converted
     * based on the type of this variable.
     */
    public <T> T getValue() {

        return (T) boundValue;
    }

    public String getVariableName() {

        final String rawName = variable.name().toString();
        final int lastColon = rawName.lastIndexOf(':');

        if (lastColon != -1) {
            return rawName.substring(lastColon + 1);
        } else {
            return rawName;
        }
    }

    /**
     * @return the isParameter
     */
    public boolean isParameter() {
        return isParameter;
    }

    /**
     * @param isParameter
     *            the isParameter to set
     */
    public void setParameter(final boolean isParameter) {
        this.isParameter = isParameter;
    }

    /**
     * Sets the {@link ModelInstance} of which this variable forms a field.
     * FIXME: this should not be assignable at all, violates abstraction.
     * 
     * @param parentModelInstance
     */
    public void setParentModelInstance(final ModelInstance parentModelInstance) {

        this.parentModelInstance = parentModelInstance;
    }

    /**
     * Sets the value of this variable. TODO: Add type checking?
     * 
     * @param value
     */
    public void setValue(final Object value) {

        boundValue = value;
    }

    @Override
    public String toString() {

        return getTypeName() + " : " + identifier;
    }

    public KeYJavaType getType() {
        return variable.getKeYJavaType();
    }
}