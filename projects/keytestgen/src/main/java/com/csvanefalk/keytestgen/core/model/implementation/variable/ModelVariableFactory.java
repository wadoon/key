package com.csvanefalk.keytestgen.core.model.implementation.variable;

import com.csvanefalk.keytestgen.core.model.implementation.instance.ModelInstance;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;

/**
 * Created by christopher on 09/01/14.
 * <p/>
 * Creates instances of the ModelVariable class.
 */
public class ModelVariableFactory {

    /**
     * Factory method for creating a {@link ModelVariable} instance.
     *
     * @param programVariable the {@link de.uka.ilkd.key.logic.op.IProgramVariable} instance which will be wrapped by
     *                        the created instance.
     * @param identifier      a unique identifier for the variable.
     * @return the created instance.
     */
    public static ModelVariable constructModelVariable(final IProgramVariable programVariable,
                                                       final String identifier) {

        if (programVariable.getKeYJavaType().getSort() instanceof ArraySort) {
            return new ModelArrayVariable(programVariable, identifier);
        } else {
            return new ModelVariable(programVariable, identifier);
        }
    }

    public static boolean isValidValueType(final Object object) {

        return ((object == null)
                || (object instanceof ModelInstance))
                || (object.getClass() == Integer.class)
                || (object.getClass() == Byte.class)
                || (object.getClass() == Long.class)
                || (object.getClass() == Boolean.class);
    }

    public static ModelVariable constructModelVariable(final ProgramVariable programVariable) {
        return ModelVariableFactory.constructModelVariable(programVariable, programVariable.name().toString());
    }
}
