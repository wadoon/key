package de.uka.ilkd.key.testgeneration.model.implementation;

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
public class ModelInstance implements IHeapObject {

    private boolean debug;
    
    /**
     * @return the debug
     */
    public boolean isDebug() {
        return debug;
    }

    /**
     * @param debug the debug to set
     */
    public void setDebug(boolean debug) {
        this.debug = debug;
    }

    /**
     * The type of which this instance is an instance.
     */
    private final KeYJavaType type;

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
     * Concrete values for a subset of the fields bound to this instance.
     */
    private final List<ModelVariable> fields = new LinkedList<ModelVariable>();

    /**
     * Creates a new ModelInstance, corresponding to an object of type
     * {@link KeYJavaType} together with a unique identifier.
     * 
     * @param type
     *            the type of the instance
     */
    public ModelInstance(KeYJavaType keYJavaType) {

        this.type = keYJavaType;
        this.identifier = Integer.toString(hashCode());
    }

    /**
     * @return the type
     */
    @Override
    public String getType() {

        return type.getJavaType().getFullName();
    }

    public String getTypeName() {

        String fullName = type.getJavaType().getFullName();
        return fullName.substring(fullName.lastIndexOf('.')+1);
    }

    /**
     * @return the fields
     */
    public List<ModelVariable> getFields() {

        return new LinkedList<ModelVariable>(fields);
    }

    public void addField(ModelVariable variable) {

        if (!fields.contains(variable)) {
            fields.add(variable);
        }
    }

    @Override
    public String getName() {

        return identifier;
    }

    /*
     * FIXME: the abstraction is broken here
     * 
     * @see de.uka.ilkd.key.testgeneration.model.IModelObject#getValue()
     */
    @Override
    public Object getValue() {

        return identifier;
    }

    @Override
    public String getIdentifier() {

        return identifier;
    }
    
    public void addReferee(ModelVariable referee) {
        referees.add(referee);
    }
    
    public List<ModelVariable> getReferees() {
        return referees;
    }

    /**
     * Two instances are equal iff. their references are the same (compare
     * reference equality in Java).
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
        ModelInstance other = (ModelInstance) obj;
        return this.identifier.equals(other.identifier);
    }

    @Override
    public String toString() {

        return "Instance " + identifier;
    }
}
