package se.gu.svanefalk.testgeneration.util.transformers;

import se.gu.svanefalk.testgeneration.util.parsers.TermParserException;

public class TermTransformerException extends TermParserException {

    private static final long serialVersionUID = -2825761961260283914L;

    public TermTransformerException(final String message) {
        super(message);
    }
}
