package se.gu.svanefalk.testgeneration.core.oracle;

import se.gu.svanefalk.testgeneration.KeYTestGenException;

/**
 * Base class for all exceptions thrown by the oracle generation subsystem.
 * 
 * @author christopher
 * 
 */
public class OracleGeneratorException extends KeYTestGenException {

    private static final long serialVersionUID = 1L;

    /**
     * Construct a new oracle generator exception.
     * 
     * @param message
     */
    public OracleGeneratorException(final String message) {
        super(message);
    }
}
