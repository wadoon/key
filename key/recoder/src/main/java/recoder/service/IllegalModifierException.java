package recoder.service;

import recoder.ModelException;

public class IllegalModifierException extends ModelException {
    private static final long serialVersionUID = -2930910039583684560L;

    public IllegalModifierException() {
    }

    public IllegalModifierException(String s) {
        super(s);
    }
}
