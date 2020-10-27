package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

public class Transient extends Modifier {
    private static final long serialVersionUID = 3518754803226194289L;

    public Transient() {
    }

    protected Transient(Transient proto) {
        super(proto);
    }

    public Transient deepClone() {
        return new Transient(this);
    }

    public void accept(SourceVisitor v) {
        v.visitTransient(this);
    }
}
