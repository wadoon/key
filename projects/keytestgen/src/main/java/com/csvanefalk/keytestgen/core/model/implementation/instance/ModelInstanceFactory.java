package com.csvanefalk.keytestgen.core.model.implementation.instance;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.sort.ArraySort;

/**
 * Created by christopher on 09/01/14.
 */
public class ModelInstanceFactory {

    /**
     * Factory method for creating a new {@link ModelInstance} instance.
     *
     * @param keYJavaType the {@link de.uka.ilkd.key.java.abstraction.KeYJavaType} instance associated with the created
     *                    instance.
     * @return the created instance.
     */
    public static ModelInstance constructModelInstance(final KeYJavaType keYJavaType) {

        if (keYJavaType.getSort() instanceof ArraySort) {
            return new ModelArrayInstance(keYJavaType);
        }

        return new ModelInstance(keYJavaType);
    }
    
    
}
