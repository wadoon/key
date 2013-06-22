package se.gu.svanefalk.testgeneration.core.model;

import se.gu.svanefalk.testgeneration.KeYTestGenException;

/**
 * Base class for all exceptions thrown by the model generation subsystem.
 * 
 * @author christopher
 * 
 */
public class ModelGeneratorException extends KeYTestGenException {

    private static final long serialVersionUID = -1461342583588654052L;

    public ModelGeneratorException(final String message) {

        super(message);
    }
}
