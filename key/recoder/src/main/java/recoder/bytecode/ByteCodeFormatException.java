package recoder.bytecode;

import recoder.ParserException;

public class ByteCodeFormatException extends ParserException {
    private static final long serialVersionUID = -6748189319137209773L;

    public ByteCodeFormatException() {
    }

    public ByteCodeFormatException(String msg) {
        super(msg);
    }
}
