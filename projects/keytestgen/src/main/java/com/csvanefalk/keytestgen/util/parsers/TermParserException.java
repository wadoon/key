package com.csvanefalk.keytestgen.util.parsers;

import com.csvanefalk.keytestgen.KeYTestGenException;

/**
 * Base class for all exceptions thrown by the various KeYTestGen2 term parsers.
 *
 * @author christopher
 */
public class TermParserException extends KeYTestGenException {

    private static final long serialVersionUID = 6540620830498122708L;

    public TermParserException(final String message) {
        super(message);
        // TODO Auto-generated constructor stub
    }
}
