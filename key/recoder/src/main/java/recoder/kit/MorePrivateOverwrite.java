package recoder.kit;

import recoder.abstraction.Method;

public class MorePrivateOverwrite extends Conflict {
    private static final long serialVersionUID = 8547386567851667884L;

    private final Method method;

    public MorePrivateOverwrite(Method method) {
        this.method = method;
    }

    public Method getMethod() {
        return this.method;
    }
}
