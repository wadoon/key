package recoder.java.expression.literal;

import recoder.java.NonTerminalProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;

public class StringLiteral extends Literal implements ReferencePrefix {
    private static final long serialVersionUID = 7368137274068211543L;

    protected ReferenceSuffix referenceParent;

    protected String value;

    public StringLiteral() {
        setValue("");
    }

    public StringLiteral(String value) {
        setValue(value);
    }

    protected StringLiteral(StringLiteral proto) {
        super(proto);
        this.value = proto.value;
    }

    public StringLiteral deepClone() {
        return new StringLiteral(this);
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.expressionParent != null)
            return this.expressionParent;
        return this.referenceParent;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.referenceParent;
    }

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.referenceParent = path;
    }

    public String getValue() {
        return this.value;
    }

    public void setValue(String str) {
        if (!str.startsWith("\"") || !str.endsWith("\""))
            throw new IllegalArgumentException("Bad string literal " + this.value);
        this.value = str.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitStringLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return this.value;
    }
}
