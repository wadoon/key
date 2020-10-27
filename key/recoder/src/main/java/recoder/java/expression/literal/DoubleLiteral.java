package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public class DoubleLiteral extends Literal {
    private static final long serialVersionUID = 6628200854323360553L;

    protected String value;

    public DoubleLiteral() {
        setValue("0.0");
    }

    public DoubleLiteral(double value) {
        setValue("" + value);
    }

    public DoubleLiteral(String value) {
        setValue(value);
    }

    protected DoubleLiteral(DoubleLiteral proto) {
        super(proto);
        this.value = proto.value;
    }

    public DoubleLiteral deepClone() {
        return new DoubleLiteral(this);
    }

    public String getValue() {
        return this.value;
    }

    public void setValue(String str) {
        this.value = str.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitDoubleLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Double.valueOf(this.value);
    }
}
