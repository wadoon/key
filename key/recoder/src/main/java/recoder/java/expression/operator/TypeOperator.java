package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.ProgramElement;
import recoder.java.expression.Operator;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;

public abstract class TypeOperator extends Operator implements TypeReferenceContainer {
    protected TypeReference typeReference;

    public TypeOperator() {
    }

    public TypeOperator(Expression unaryChild, TypeReference typeref) {
        super(unaryChild);
        setTypeReference(typeref);
    }

    public TypeOperator(Expression lhs, Expression rhs, TypeReference typeref) {
        super(lhs, rhs);
        setTypeReference(typeref);
    }

    protected TypeOperator(TypeOperator proto) {
        super(proto);
        if (proto.typeReference != null)
            this.typeReference = proto.typeReference.deepClone();
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.typeReference != null)
            this.typeReference.setParent(this);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.children != null) {
            int index = this.children.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        if (this.typeReference == child)
            return 1;
        return -1;
    }

    public int getTypeReferenceCount() {
        return (this.typeReference != null) ? 1 : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.typeReference != null && index == 0)
            return this.typeReference;
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.children == null) ? 0 : this.children.size();
        for (int i = 0; i < count; i++) {
            if (this.children.get(i) == p) {
                if (q == null) {
                    this.children.remove(i);
                } else {
                    Expression r = (Expression) q;
                    this.children.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        if (this.typeReference == p) {
            TypeReference r = (TypeReference) q;
            this.typeReference = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        return false;
    }

    public TypeReference getTypeReference() {
        return this.typeReference;
    }

    public void setTypeReference(TypeReference t) {
        this.typeReference = t;
    }
}
