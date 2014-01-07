package com.csvanefalk.keytestgen.util.visitors;

import com.csvanefalk.keytestgen.KeYTestGenException;

public class XMLVisitorException extends KeYTestGenException {

    private static final long serialVersionUID = -286893052052896384L;

    public XMLVisitorException(final String message) {

        super(message);
    }

    public XMLVisitorException(final String message, final Throwable cause) {
        super(message, cause);

    }
}
