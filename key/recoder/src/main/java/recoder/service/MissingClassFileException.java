package recoder.service;

import recoder.ModelException;

public class MissingClassFileException extends ModelException {
    private static final long serialVersionUID = 3265837360603622631L;

    private final String missingClass;

    public MissingClassFileException(String name) {
        this.missingClass = name;
    }

    public MissingClassFileException(String s, String name) {
        super(s);
        this.missingClass = name;
    }

    public String getMissingClassFileName() {
        return this.missingClass;
    }
}
