package recoder.kit;

import recoder.abstraction.Method;

public class DifferentReturnTypeOverwrite extends Conflict {
    private static final long serialVersionUID = 1569165840299545025L;

    private final Method method;

    public DifferentReturnTypeOverwrite(Method method) {
        this.method = method;
    }

    public Method getMethod() {
        return this.method;
    }
}
