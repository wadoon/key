package de.uka.ilkd.key.testgeneration.model.implementation;

import de.uka.ilkd.key.testgeneration.model.IModelVariable;

public class ModelVariable
        implements IModelVariable {

    private final String name;
    private final String type;
    private final Object value;
    private final IModelVariable parent;

    public ModelVariable(
            String name,
            String type,
            Object value,
            IModelVariable parent) {

        super();
        this.name = name;
        this.type = type;
        this.value = value;
        this.parent = parent;
    }

    @Override
    public String getName() {

        return name;
    }

    @Override
    public String getType() {

        return type;
    }

    @Override
    public Object getValue() {

        return value;
    }

    @Override
    public IModelVariable getParent() {

        return parent;
    }

    @Override
    public String toString() {

        return parent.getName()+"."+name;
    }
}
