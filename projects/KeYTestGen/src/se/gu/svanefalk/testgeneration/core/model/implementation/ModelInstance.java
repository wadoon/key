package se.gu.svanefalk.testgeneration.core.model.implementation;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;

/**
 * Instances of this class represent concrete Java objects on the heap. Such
 * instances are necessarily unique (as they would be in Java) and contain
 * information about the state of the object. Importantly, it stores the
 * concrete values of any fields its class may have, as well as information
 * about the {@link ModelVariable} instances referring to it.
 * 
 * @author christopher
 */
public class ModelInstance {

    /**
     * Used for generating unique IDs for model instances.
     */
    private static int ID = 0;

    /**
     * Factory method for creating a new {@link ModelInstance} instance.
     * 
     * @param keYJavaType
     *            the {@link KeYJavaType} instance associated with the created
     *            instance.
     * @return the created instance.
     */
    public static ModelInstance constructModelInstance(
            final KeYJavaType keYJavaType) {

        return new ModelInstance(keYJavaType);
    }

    /**
     * Concrete values for a subset of the fields bound to this instance.
     */
    private final List<ModelVariable> fields = new LinkedList<ModelVariable>();

    /**
     * A unique identifier for this particular instance. Think of it as the
     * memory address of an actual Java object on the heap.
     */
    private final String identifier;

    /**
     * Variables pointing to this instance
     */
    private final List<ModelVariable> referees = new LinkedList<ModelVariable>();

    /**
     * The type of which this instance is an instance.
     */
    private final KeYJavaType type;

    private ModelInstance(final KeYJavaType keYJavaType) {

        type = keYJavaType;
        identifier = Integer.toString(++ModelInstance.ID);
    }

    public void addField(final ModelVariable variable) {

        if (!fields.contains(variable)) {
            fields.add(variable);
        }
    }

    public void addReferee(final ModelVariable referee) {
        referees.add(referee);
    }

    /**
     * Two instances are equal iff. their references are the same (compare
     * reference equality in Java).
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
        final ModelInstance other = (ModelInstance) obj;
        return identifier.equals(other.identifier);
    }

    /**
     * @return the fields
     */
    public List<ModelVariable> getFields() {

        return new LinkedList<ModelVariable>(fields);
    }

    public String getIdentifier() {

        return identifier;
    }

    public List<ModelVariable> getReferees() {
        return referees;
    }

    /**
     * @return the type
     */
    public String getType() {

        return type.getJavaType().getFullName();
    }

    public String getTypeName() {

        return type.getJavaType().getName().toString();
    }

    @Override
    public String toString() {

        return "Instance " + identifier;
    }
}
