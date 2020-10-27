package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;

public class Private extends VisibilityModifier {
    private static final long serialVersionUID = -7858559458205603231L;

    public Private() {
    }

    protected Private(Private proto) {
        super(proto);
    }

    public Private deepClone() {
        return new Private(this);
    }

    public void accept(SourceVisitor v) {
        v.visitPrivate(this);
    }
}
