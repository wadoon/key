package com.csvanefalk.keytestgen.core.oracle;

import com.csvanefalk.keytestgen.KeYTestGenException;

/**
 * Base class for all exceptions thrown by the oracle generation subsystem.
 *
 * @author christopher
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
