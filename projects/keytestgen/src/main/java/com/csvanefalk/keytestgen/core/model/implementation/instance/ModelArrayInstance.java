package com.csvanefalk.keytestgen.core.model.implementation.instance;

import com.csvanefalk.keytestgen.StringConstants;
import com.csvanefalk.keytestgen.core.model.implementation.variable.ModelVariable;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

import java.util.List;

/**
 * Represents a concrete instance of a Java array.
 */
public class ModelArrayInstance extends ModelInstance {

    public ModelArrayInstance(KeYJavaType keYJavaType) {
        super(keYJavaType);
    }

    /**
     * Gets the length of this array. If the length is defined explicitly in connection
     * with creating this instance, then this specific value is used. Otherwise, the standard
     * size of the associated elements is used.
     *
     * @return the length of this array.
     */
    public int length() {
        for (ModelVariable field : getFields()) {
            if (field.getVariableName().endsWith(StringConstants.LENGTH)) {
                return field.getValue();
            }
        }
        return getFields().size();
    }

    /**
     * @return all elements of this array.
     */
    public List<ModelVariable> getArrayElements() {
        return null;
    }

    /**
     * Gets an element of this array instance by index.
     *
     * @param index index of the elements.
     * @return the elements, or null if no element exists for the provided index.
     */
    public ModelVariable getElement(int index) {
        return null;
    }
}
