package de.uka.ilkd.key.testgeneration.defaultimplementation;

public class ModelVariable
        implements IModelVariable {

    private final String name;
    private final String type;
    private final Object value;
    private final ModelReferenceVariable parent;

    public ModelVariable(
            String name,
            String type,
            Object value,
            ModelReferenceVariable parent) {
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
    public IModelReferenceVariable getParent() {
        return parent;
    }
}
