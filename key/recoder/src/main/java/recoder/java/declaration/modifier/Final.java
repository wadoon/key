package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

public class Final extends Modifier {
    private static final long serialVersionUID = 7169854150660337404L;

    public Final() {
    }

    protected Final(Final proto) {
        super(proto);
    }

    public Final deepClone() {
        return new Final(this);
    }

    public void accept(SourceVisitor v) {
        v.visitFinal(this);
    }
}
