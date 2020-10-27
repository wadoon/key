package recoder.service;

import recoder.ModelException;
import recoder.abstraction.ClassType;

public class CyclicInheritanceException extends ModelException {
    private static final long serialVersionUID = -2917658612032872699L;

    private final ClassType baseClass;

    public CyclicInheritanceException(ClassType ct) {
        this.baseClass = ct;
    }

    public CyclicInheritanceException(String s, ClassType ct) {
        super(s);
        this.baseClass = ct;
    }

    public ClassType getSelfInheritingType() {
        return this.baseClass;
    }
}
