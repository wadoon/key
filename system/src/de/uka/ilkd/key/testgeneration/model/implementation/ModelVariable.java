package de.uka.ilkd.key.testgeneration.model.implementation;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.IModelVariable;

/**
 * The default implementation of {@link IModelVariable}.
 * <p>
 * This class encapsulates the actual {@link ProgramVariable} instance for the variable which it
 * represents. On top of the information contained in this wrapped instance, this class adds a bound
 * value, as well as parent-children references, allowing instances of this class to be organized as
 * a tree.This is done in order to represent declaration hierarchies in an actual Java program.
 * 
 * @author christopher
 */
public class ModelVariable
        implements IModelVariable {

    /**
     * The {@link ProgramVariable} instance wrapped by this variable
     */
    private ProgramVariable wrappedProgramVariable;

    /**
     * A unique identifier related to the particular implementation of {@link IModel} we are using
     * (i.e. {@link Model}).
     */
    private final String identifier;

    /**
     * The value bound to this object. Primitive types are represented by their wrapper types (
     * {@link Integer}, {@link Boolean} etc).
     */
    private Object boundValue;

    /**
     * The parent of this value
     */
    private ModelVariable parent;

    /**
     * The children bound to this node. Such a child can correspond to one and only one of this
     * types fields.T
     */
    private List<ModelVariable> children = new LinkedList<ModelVariable>();

    /**
     * Create a ModelVariable from an existing {@link ProgramVariable}, effectively encapsulating
     * it, but we maintain the type hierarchy for the sake of consistency.
     * 
     * @param programVariable
     */
    public ModelVariable(
            ProgramVariable programVariable,
            ModelVariable parent,
            String identifier) {

        this.wrappedProgramVariable = programVariable;
        this.parent = parent;
        this.identifier = identifier;
    }

    @Override
    public String getName() {

        return wrappedProgramVariable.name().toString();
    }

    /**
     * Returns a String representation of the {@link KeYJavaType} of this variable.
     */
    @Override
    public String getType() {

        return wrappedProgramVariable.getKeYJavaType().getFullName();
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
     * Returns the value of the variable. Will have to be explicitly converted based on the type of
     * this variable.
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
     * Returns the parent {@link ModelVariable} of this variable.
     * 
     * @return
     */
    public ModelVariable getParent() {

        return parent;
    }

    /**
     * @return the children of this variable
     */
    public List<ModelVariable> getChildren() {

        return children;
    }

    /**
     * Add a child {@link ModelVariable} to this variable
     * 
     * @param child
     *            the child to add
     */
    public void addChild(ModelVariable child) {

        if (!children.contains(child)) {
            children.add(child);
        }
    }

    @Override
    public String toString() {

        return wrappedProgramVariable.toString() + " (id=" + identifier + ")";
    }

    /**
     * Returns the unique identifier of this variable.
     * 
     * @return the identifier String
     */
    public String getId() {

        return identifier;
    }

    /**
     * Since we are working with unique Java statements, two {@link ModelVariable} instances are
     * equal iff. their identifiers are identical.
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
}
