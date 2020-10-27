package recoder.kit;

import recoder.abstraction.Method;

public class UncoveredExceptionsOverwrite extends Conflict {
    private static final long serialVersionUID = 1648909642243255075L;

    private final Method method;

    public UncoveredExceptionsOverwrite(Method method) {
        this.method = method;
    }

    public Method getMethod() {
        return this.method;
    }
}
