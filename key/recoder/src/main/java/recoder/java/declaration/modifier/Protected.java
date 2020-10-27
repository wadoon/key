package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;

public class Protected extends VisibilityModifier {
    private static final long serialVersionUID = 294440790233996705L;

    public Protected() {
    }

    protected Protected(Protected proto) {
        super(proto);
    }

    public Protected deepClone() {
        return new Protected(this);
    }

    public void accept(SourceVisitor v) {
        v.visitProtected(this);
    }
}
