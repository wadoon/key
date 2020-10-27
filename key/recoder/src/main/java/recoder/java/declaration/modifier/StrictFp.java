package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

public class StrictFp extends Modifier {
    private static final long serialVersionUID = 6903473464189070008L;

    public StrictFp() {
    }

    protected StrictFp(StrictFp proto) {
        super(proto);
    }

    public StrictFp deepClone() {
        return new StrictFp(this);
    }

    public void accept(SourceVisitor v) {
        v.visitStrictFp(this);
    }
}
