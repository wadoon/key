package com.csvanefalk.keytestgen.core.model.implementation.instance;

import com.csvanefalk.keytestgen.StringConstants;
import com.csvanefalk.keytestgen.core.model.implementation.variable.ModelVariable;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

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
            if (field.getVariableName().equalsIgnoreCase(StringConstants.LENGTH)) {
                return field.getValue();
            }
        }
        return getFields().size();
    }
}
