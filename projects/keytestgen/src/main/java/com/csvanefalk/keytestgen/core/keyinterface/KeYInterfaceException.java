package com.csvanefalk.keytestgen.core.keyinterface;

import com.csvanefalk.keytestgen.KeYTestGenException;

/**
 * Base class for all exceptions thrown by the KeY interface subsystem.
 *
 * @author christopher
 */
public class KeYInterfaceException extends KeYTestGenException {

    private static final long serialVersionUID = 2393311991899525271L;

    public KeYInterfaceException(final String message) {
        super(message);
    }
}
