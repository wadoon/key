package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public class FloatLiteral extends Literal {
    private static final long serialVersionUID = 9215865599908556320L;

    protected String value;

    public FloatLiteral() {
        setValue("0.0F");
    }

    public FloatLiteral(float value) {
        setValue("" + value + 'F');
    }

    public FloatLiteral(String value) {
        setValue((value.endsWith("F") || value.endsWith("f")) ? value : (value + 'F'));
    }

    protected FloatLiteral(FloatLiteral proto) {
        super(proto);
        this.value = proto.value;
    }

    public FloatLiteral deepClone() {
        return new FloatLiteral(this);
    }

    public String getValue() {
        return this.value;
    }

    public void setValue(String str) {
        this.value = str.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitFloatLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Float.valueOf(this.value);
    }
}
