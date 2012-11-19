package de.uka.ilkd.key.testgeneration.model.implementation;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.IModelVariable;

public class ModelVariable
        implements IModelVariable {

    /**
     * A unique identifier related to the particular implementation of {@link IModel} we are using (i.e. {@link Model}).
     */
    private final String identifier;

    /**
     * The {@link ProgramVariable} instance wrapped by this variable
     */
    private ProgramVariable wrappedProgramVariable;

    /**
     * The value bound to this object. The wrapper types are used in order to represent primitive
     * types.
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

    @Override
    public String getType() {

        return wrappedProgramVariable.getKeYJavaType().getFullName();
    }

    @Override
    public Object getValue() {

        return boundValue;
    }
    
    public void setValue(Object value) {
        this.boundValue = value;
    }

    public ModelVariable getParent() {

        return parent;
    }

    public List<ModelVariable> getChildren() {

        return children;
    }

    public void addChild(ModelVariable child) {

        if (!children.contains(child)) {
            children.add(child);
        }
    }

    @Override
    public String toString() {

        return wrappedProgramVariable.toString() + " (id=" + identifier + ")";
    }
    
    public String getId() {
        return identifier;
    }
    
    /**
     * Since we are working with unique Java statements, two {@link ModelVariable} instances are
     * equal iff. the {@link ProgramVariable} instances they wrap are exactly the same object.
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
