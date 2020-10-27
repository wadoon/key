package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

public class Native extends Modifier {
    private static final long serialVersionUID = -5292363142166406788L;

    public Native() {
    }

    protected Native(Native proto) {
        super(proto);
    }

    public Native deepClone() {
        return new Native(this);
    }

    public void accept(SourceVisitor v) {
        v.visitNative(this);
    }
}
