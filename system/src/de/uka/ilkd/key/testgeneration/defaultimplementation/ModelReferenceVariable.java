package de.uka.ilkd.key.testgeneration.defaultimplementation;

import java.util.LinkedList;
import java.util.List;

public class ModelReferenceVariable
        extends ModelVariable
        implements IModelReferenceVariable {

    private final String objectPackage;
    private final LinkedList<IModelVariable> fields = new LinkedList<>();

    public ModelReferenceVariable(
            String name,
            String type,
            Object value,
            ModelReferenceVariable parent,
            String objectPackage) {
        super(name, type, value, parent);
        this.objectPackage = objectPackage;
    }

    @Override
    public String getPackage() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public List<IModelVariable> getFields() {
        // TODO Auto-generated method stub
        return null;
    }

    public void addField(IModelReferenceVariable field) {
        fields.add(field);
    }
}