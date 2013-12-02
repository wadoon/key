package com.csvanefalk.keytestgen.util.transformers;

import com.csvanefalk.keytestgen.util.parsers.TermParserException;

public class TermTransformerException extends TermParserException {

    private static final long serialVersionUID = -2825761961260283914L;

    public TermTransformerException(final String message) {
        super(message);
    }
}
