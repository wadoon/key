package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public class LongLiteral extends Literal {
    private static final long serialVersionUID = -8507020453717633759L;

    protected String value;

    public LongLiteral() {
        setValue("0L");
    }

    public LongLiteral(long value) {
        setValue("" + value + 'L');
    }

    public LongLiteral(String value) {
        setValue((value.endsWith("L") || value.endsWith("l")) ? value : (value + 'L'));
    }

    protected LongLiteral(LongLiteral proto) {
        super(proto);
        this.value = proto.value;
    }

    public LongLiteral deepClone() {
        return new LongLiteral(this);
    }

    public String getValue() {
        return this.value;
    }

    public void setValue(String str) {
        this.value = str.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitLongLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Long.valueOf(this.value);
    }
}
