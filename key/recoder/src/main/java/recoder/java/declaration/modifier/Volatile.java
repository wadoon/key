package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

public class Volatile extends Modifier {
    private static final long serialVersionUID = -8915246411373317235L;

    public Volatile() {
    }

    protected Volatile(Volatile proto) {
        super(proto);
    }

    public Volatile deepClone() {
        return new Volatile(this);
    }

    public void accept(SourceVisitor v) {
        v.visitVolatile(this);
    }
}
