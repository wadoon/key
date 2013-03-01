package de.uka.ilkd.key.testgeneration.core.model.implementation;

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

    public static boolean isValidValueType(final Object object) {

        return object.getClass() == ModelInstance.class
                || object.getClass() == Integer.class
                || object.getClass() == Byte.class
                || object.getClass() == Long.class
                || object.getClass() == Boolean.class;
    }

    /**
     * The wrapped {@link ProgramVariable} instance.
     */
    private final IProgramVariable variable;

    /**
     * Represents a unique identifier for this variable, denoting its relative
     * point of declaration in the program, in the form
     * self_dot_someField_dot_someOtherField_dot_thisvariable. Since no two
     * variables can have the same declaration space, this is also used to
     * uniquely distinguish this variable as a {@link IHeapObject}.
     */
    private final String identifier;

    /**
     * The value bound to this object. Primitive types are represented by their
     * wrapper types ( {@link Integer}, {@link Boolean} etc).
     */
    private Object boundValue;

    /**
     * The instance of {@link ModelInstance} in which this particular instance
     * of {@link ModelVariable} has been initialized.
     */
    private ModelInstance parentModelInstance;

    /**
     * This flag indicates whether or not this variable is declared in the
     * parameter list for a method.
     */
    private boolean isParameter = false;

    public ModelVariable(final IProgramVariable programVariable,
            final String identifier) {

        this(programVariable, identifier, null);
    }

    /**
     * Create a ModelVariable from an existing {@link ProgramVariable},
     * effectively encapsulating it, but we maintain the type hierarchy for the
     * sake of consistency.
     * 
     * @param programVariable
     */
    public ModelVariable(final IProgramVariable programVariable,
            final String identifier, final ModelInstance referedInstance) {

        variable = programVariable;

        this.identifier = identifier;
        boundValue = referedInstance;

    }

    /**
     * Since we are working with unique Java statements, two
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
        if (getClass() != obj.getClass()) {
            return false;
        }
        final ModelVariable other = (ModelVariable) obj;
        return identifier.equals(other.identifier);
    }

    /**
     * A variable is uniquely identified by its identifier.
     */
    public String getIdentifier() {

        return variable.name().toString();
    }

    public String getName() {

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
    public String getType() {

        return variable.getKeYJavaType().getName();
    }

    /**
     * Returns the value of the variable. Will have to be explicitly converted
     * based on the type of this variable.
     */
    public Object getValue() {

        return boundValue;
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

        return getType() + " : " + identifier;
    }
}