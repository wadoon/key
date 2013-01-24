package de.uka.ilkd.key.testgeneration.visitors;

import de.uka.ilkd.key.testgeneration.KeYTestGenException;

public class XMLVisitorException extends KeYTestGenException {

    private static final long serialVersionUID = -286893052052896384L;

    public XMLVisitorException(String message) {

        super(message);
    }

    public XMLVisitorException(String message, Throwable cause) {
        super(message, cause);

    }
}
