package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

public class Synchronized extends Modifier {
    private static final long serialVersionUID = -4425302603634609276L;

    public Synchronized() {
    }

    protected Synchronized(Synchronized proto) {
        super(proto);
    }

    public Synchronized deepClone() {
        return new Synchronized(this);
    }

    public void accept(SourceVisitor v) {
        v.visitSynchronized(this);
    }
}
