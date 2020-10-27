package recoder.service;

import recoder.ModelException;
import recoder.kit.Transformation;

public class NoSuchTransformationException extends ModelException {
    private static final long serialVersionUID = 1118670095981879663L;

    public NoSuchTransformationException() {
    }

    public NoSuchTransformationException(Transformation transformation) {
        this("Transformation not found: " + transformation.toString());
    }

    public NoSuchTransformationException(String s) {
        super(s);
    }
}
