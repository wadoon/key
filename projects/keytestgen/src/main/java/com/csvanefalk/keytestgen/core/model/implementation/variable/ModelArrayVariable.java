package com.csvanefalk.keytestgen.core.model.implementation.variable;

import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * Created by christopher on 09/01/14.
 * <p/>
 * Represents a primitive Java array. Can hold either primitive or reference
 * type elements.
 */
public class ModelArrayVariable extends ModelVariable {

    ModelArrayVariable(final IProgramVariable programVariable,
                       final String identifier) {
        super(programVariable, identifier);
    }
}