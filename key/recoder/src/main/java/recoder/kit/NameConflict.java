package recoder.kit;

import recoder.NamedModelElement;

public class NameConflict extends Conflict {
    private static final long serialVersionUID = -2147929685769271562L;

    private final NamedModelElement reason;

    public NameConflict(NamedModelElement reason) {
        this.reason = reason;
    }

    public NamedModelElement getReason() {
        return this.reason;
    }
}
