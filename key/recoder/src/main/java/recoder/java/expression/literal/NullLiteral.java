package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public class NullLiteral extends Literal {
    private static final long serialVersionUID = -1679522775179075816L;

    public NullLiteral() {
    }

    protected NullLiteral(NullLiteral proto) {
        super(proto);
    }

    public NullLiteral deepClone() {
        return new NullLiteral(this);
    }

    public void accept(SourceVisitor v) {
        v.visitNullLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return null;
    }
}
