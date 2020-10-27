package recoder.service;

import recoder.ModelException;
import recoder.ParserException;

public class TypeImportException extends ModelException {
    private static final long serialVersionUID = 7615714671292466231L;

    public TypeImportException() {
    }

    public TypeImportException(String s) {
        super(s);
    }

    public TypeImportException(ParserException p) {
        super(p.toString());
    }
}
