package recoder.kit.pattern;

import recoder.ModelException;

public class InconsistentPatternException extends ModelException {
    private static final long serialVersionUID = 1L;

    public InconsistentPatternException() {
    }

    public InconsistentPatternException(String s) {
        super(s);
    }
}
