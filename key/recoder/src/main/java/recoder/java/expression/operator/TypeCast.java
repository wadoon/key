package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;

public class TypeCast extends TypeOperator {
    private static final long serialVersionUID = 2209252813347809519L;

    public TypeCast() {
    }

    public TypeCast(Expression child, TypeReference typeref) {
        super(child, typeref);
        makeParentRoleValid();
    }

    protected TypeCast(TypeCast proto) {
        super(proto);
        makeParentRoleValid();
    }

    public TypeCast deepClone() {
        return new TypeCast(this);
    }

    public int getChildCount() {
        int result = 0;
        if (this.typeReference != null)
            result++;
        if (this.children != null)
            result += this.children.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.typeReference != null) {
            if (index == 0)
                return this.typeReference;
            index--;
        }
        if (this.children != null) {
            int len = this.children.size();
            if (len > index)
                return this.children.get(index);
            index -= len;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getArity() {
        return 1;
    }

    public int getPrecedence() {
        return 1;
    }

    public int getNotation() {
        return 0;
    }

    public boolean isLeftAssociative() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitTypeCast(this);
    }
}
