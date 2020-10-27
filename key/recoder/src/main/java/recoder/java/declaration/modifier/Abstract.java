package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

public class Abstract extends Modifier {
    private static final long serialVersionUID = -380790417611526476L;

    public Abstract() {
    }

    protected Abstract(Abstract proto) {
        super(proto);
    }

    public Abstract deepClone() {
        return new Abstract(this);
    }

    public void accept(SourceVisitor v) {
        v.visitAbstract(this);
    }
}
