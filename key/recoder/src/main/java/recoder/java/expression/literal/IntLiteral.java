package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public class IntLiteral extends Literal {
    private static final long serialVersionUID = -5285529378094375335L;

    protected String value;

    public IntLiteral() {
        setValue("0");
    }

    public IntLiteral(int value) {
        setValue("" + value);
    }

    public IntLiteral(String value) {
        setValue(value);
    }

    protected IntLiteral(IntLiteral proto) {
        super(proto);
        this.value = proto.value;
    }

    public IntLiteral deepClone() {
        return new IntLiteral(this);
    }

    public String getValue() {
        return this.value;
    }

    public void setValue(String str) {
        this.value = str.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitIntLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Integer.valueOf(this.value);
    }
}
