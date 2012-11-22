package de.uka.ilkd.key.testgeneration.model.implementation;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.testgeneration.model.IModelObject;

/**
 * Instances of this class represent concrete Java objects on the heap. Such instances are
 * necessarily unique (as they would be in Java) and contain information about the state of the
 * object. Importantly, it stores the concrete values of any fields its class may have, as well as
 * information about the {@link ModelVariable} instances referring to it.
 * 
 * @author christopher
 */
public class ModelInstance
        implements IHeapObject {

    /**
     * The type of which this instance is an instance.
     */
    private final KeYJavaType type;

    /**
     * A unique identifier for this particular instance. Think of it as the memory address of an
     * actual Java object on the heap.
     */
    private final String identifier;

    /**
     * Concrete values for a subset of the fields bound to this instance.
     */
    private final List<ModelVariable> fields = new LinkedList<ModelVariable>();

    /**
     * Creates a new ModelInstance, corresponding to an object of type {@link KeYJavaType} together
     * with a unique identifier.
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
    public String getType() {

        return type.toString();
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

    /**
     * Two instances are equal iff. their references are the same (compare reference equality in
     * Java).
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
    
        String toReturn = "Instance " + identifier + " [";
        for(ModelVariable variable : fields) {
            toReturn += variable.toString() + " ";
        }
        return toReturn;
    }
}
