package com.csvanefalk.keytestgen.core.codecoverage;

import com.csvanefalk.keytestgen.KeYTestGenException;

/**
 * Base class for all exceptions thrown by the code coverage generation
 * subsystem.
 *
 * @author christopher
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
