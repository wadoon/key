package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public class CharLiteral extends Literal {
    private static final long serialVersionUID = -558509934440205638L;

    protected String value;

    public CharLiteral() {
    }

    public CharLiteral(char value) {
        setValue(value);
    }

    public CharLiteral(String value) {
        setValue(value);
    }

    protected CharLiteral(CharLiteral proto) {
        super(proto);
        this.value = proto.value;
    }

    public CharLiteral deepClone() {
        return new CharLiteral(this);
    }

    public String getValue() {
        return this.value;
    }

    public void setValue(char c) {
        setValue("'" + c + "'");
    }

    public void setValue(String str) {
        if (!str.startsWith("'") || !str.endsWith("'"))
            throw new IllegalArgumentException("Bad char literal " + this.value);
        this.value = str.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitCharLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Character.valueOf(this.value.charAt(0));
    }
}
