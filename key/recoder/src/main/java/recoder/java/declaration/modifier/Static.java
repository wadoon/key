package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

public class Static extends Modifier {
    private static final long serialVersionUID = -6125238838094732013L;

    public Static() {
    }

    protected Static(Static proto) {
        super(proto);
    }

    public Static deepClone() {
        return new Static(this);
    }

    public void accept(SourceVisitor v) {
        v.visitStatic(this);
    }
}
