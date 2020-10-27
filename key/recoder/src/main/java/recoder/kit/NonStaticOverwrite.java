package recoder.kit;

import recoder.abstraction.Method;

public class NonStaticOverwrite extends Conflict {
    private static final long serialVersionUID = -3618890938924075301L;

    private final Method method;

    public NonStaticOverwrite(Method method) {
        this.method = method;
    }

    public Method getMethod() {
        return this.method;
    }
}
