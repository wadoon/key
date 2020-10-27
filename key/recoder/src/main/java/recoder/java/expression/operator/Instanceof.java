package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;

public class Instanceof extends TypeOperator {
    private static final long serialVersionUID = 6100795662310024426L;

    public Instanceof() {
    }

    public Instanceof(Expression child, TypeReference typeref) {
        super(child, typeref);
        makeParentRoleValid();
    }

    protected Instanceof(Instanceof proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Instanceof deepClone() {
        return new Instanceof(this);
    }

    public int getChildCount() {
        int result = 0;
        if (this.children != null)
            result += this.children.size();
        if (this.typeReference != null)
            result++;
        return result;
    }

    public SourceElement getLastElement() {
        return this.typeReference.getLastElement();
    }

    public ProgramElement getChildAt(int index) {
        if (this.children != null) {
            int len = this.children.size();
            if (len > index)
                return this.children.get(index);
            index -= len;
        }
        if (this.typeReference != null) {
            if (index == 0)
                return this.typeReference;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getArity() {
        return 1;
    }

    public int getPrecedence() {
        return 5;
    }

    public int getNotation() {
        return 2;
    }

    public void accept(SourceVisitor v) {
        v.visitInstanceof(this);
    }
}
