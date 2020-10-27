package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;

public class Public extends VisibilityModifier {
    private static final long serialVersionUID = 9023181714825745478L;

    public Public() {
    }

    protected Public(Public proto) {
        super(proto);
    }

    public Public deepClone() {
        return new Public(this);
    }

    public void accept(SourceVisitor v) {
        v.visitPublic(this);
    }
}
