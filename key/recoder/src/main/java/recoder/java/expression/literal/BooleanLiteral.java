package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public class BooleanLiteral extends Literal {
    private static final long serialVersionUID = 1135231084094020816L;

    protected boolean value;

    public BooleanLiteral() {
    }

    public BooleanLiteral(boolean value) {
        setValue(value);
    }

    protected BooleanLiteral(String value) {
        if ("true".equals(value)) {
            setValue(true);
        } else if ("false".equals(value)) {
            setValue(false);
        } else {
            throw new IllegalArgumentException("Bad boolean literal " + value);
        }
    }

    protected BooleanLiteral(BooleanLiteral proto) {
        super(proto);
        this.value = proto.value;
    }

    public BooleanLiteral deepClone() {
        return new BooleanLiteral(this);
    }

    public boolean getValue() {
        return this.value;
    }

    public void setValue(boolean b) {
        this.value = b;
    }

    public void accept(SourceVisitor v) {
        v.visitBooleanLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Boolean.valueOf(this.value);
    }
}
