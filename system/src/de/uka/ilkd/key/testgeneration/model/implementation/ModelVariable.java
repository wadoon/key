package de.uka.ilkd.key.testgeneration.model.implementation;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Instances of this class represent Java program variables during runtime. It's
 * main function is to encapsulate a corresponding instance of
 * {@link ProgramVariable}, which will contain rather complete information about
 * the variable itself. However, it adds an additional layer runtime
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
public class ModelVariable implements IHeapObject {

    /**
     * Represents a unique identifier for this variable, denoting its relative
     * point of declaration in the program, in the form
     * self_dot_someField_dot_someOtherField_dot_thisvariable. Since no two
     * variables can have the same declaration space, this is also used to
     * uniquely distinguish this variable as a {@link IHeapObject}.
     */
    private final String identifier;

    /**
     * The {@link ProgramVariable} instance wrapped by this variable
     */
    private final ProgramVariable wrappedProgramVariable;

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
     * Create a ModelVariable from an existing {@link ProgramVariable},
     * effectively encapsulating it, but we maintain the type hierarchy for the
     * sake of consistency.
     * 
     * @param programVariable
     */
    public ModelVariable(ProgramVariable programVariable, String path,
            ModelInstance referedInstance) {

        this.wrappedProgramVariable = programVariable;
        this.identifier = path;
        this.boundValue = referedInstance;
    }

    public ModelVariable(ProgramVariable programVariable, String path) {

        this(programVariable, path, null);
    }

    @Override
    public String getName() {

        String parentName = wrappedProgramVariable.name().toString();
        String[] splitParentName = parentName.split("::");
        return splitParentName[splitParentName.length - 1];
    }

    /**
     * Returns a String representation of the {@link KeYJavaType} of this
     * variable.
     */
    @Override
    public String getType() {

        return wrappedProgramVariable.getKeYJavaType().getJavaType()
                .getFullName();
    }

    /**
     * Gets the actual {@link KeYJavaType} for this variable.
     * 
     * @return the {@link KeYJavaType}
     */
    public KeYJavaType getKeYJavaType() {

        return wrappedProgramVariable.getKeYJavaType();
    }

    /**
     * Returns the value of the variable. Will have to be explicitly converted
     * based on the type of this variable.
     */
    @Override
    public Object getValue() {

        return boundValue;
    }

    /**
     * Sets the value of this variable. TODO: Add type checking?
     * 
     * @param value
     */
    public void setValue(Object value) {

        this.boundValue = value;
    }

    /**
     * A variable is uniquely identified by its identifier.
     */
    @Override
    public String getIdentifier() {

        return identifier;
    }

    public static boolean isValidValueType(Object object) {

        return object.getClass() == ModelInstance.class
                || object.getClass() == Integer.class
                || object.getClass() == Byte.class
                || object.getClass() == Long.class
                || object.getClass() == Boolean.class;
    }

    /**
     * Since we are working with unique Java statements, two
     * {@link ModelVariable} instances are equal iff. their paths are identical.
     */
    @Override
    public boolean equals(Object obj) {

        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        ModelVariable other = (ModelVariable) obj;
        return this.identifier.equals(other.identifier);
    }

    @Override
    public String toString() {

        return wrappedProgramVariable.getKeYJavaType().getFullName() + " : "
                + identifier;
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
     * Sets the {@link ModelInstance} of which this variable forms a field.
     * FIXME: this should not be assignable at all, violates abstraction.
     * 
     * @param parentModelInstance
     */
    public void setParentModelInstance(ModelInstance parentModelInstance) {

        this.parentModelInstance = parentModelInstance;
    }

    /**
     * @return true if this variable is declared as static, false otherwise
     */
    public boolean isStatic() {

        return wrappedProgramVariable.isStatic();
    }

    /**
     * @return true if this variable is declared as final, false otherwise
     */
    public boolean isFinal() {

        return wrappedProgramVariable.isFinal();
    }
}
