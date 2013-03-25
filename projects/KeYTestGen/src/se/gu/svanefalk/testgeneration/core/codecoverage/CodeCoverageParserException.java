package se.gu.svanefalk.testgeneration.core.codecoverage;

import se.gu.svanefalk.testgeneration.KeYTestGenException;

/**
 * Base class for all exceptions thrown by the code coverage generation
 * subsystem.
 * 
 * @author christopher
 * 
 */
public class CodeCoverageParserException extends KeYTestGenException {

    private static final long serialVersionUID = 1L;

    /**
     * Construct a new oracle generator exception.
     * 
     * @param message
     */
    public CodeCoverageParserException(final String message) {
        super(message);
    }
}
