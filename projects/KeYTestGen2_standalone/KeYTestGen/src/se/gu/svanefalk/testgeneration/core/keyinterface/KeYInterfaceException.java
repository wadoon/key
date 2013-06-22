package se.gu.svanefalk.testgeneration.core.keyinterface;

import se.gu.svanefalk.testgeneration.KeYTestGenException;

/**
 * Base class for all exceptions thrown by the KeY interface subsystem.
 * 
 * @author christopher
 * 
 */
public class KeYInterfaceException extends KeYTestGenException {

    private static final long serialVersionUID = 2393311991899525271L;

    public KeYInterfaceException(final String message) {
        super(message);
    }
}
