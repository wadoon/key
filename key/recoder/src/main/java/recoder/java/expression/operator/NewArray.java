package recoder.java.expression.operator;

import recoder.java.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

public class NewArray extends TypeOperator implements Reference, ReferencePrefix {
    private static final long serialVersionUID = 836360320945022449L;

    protected int dimensions;

    protected ArrayInitializer arrayInitializer;

    protected ReferenceSuffix referenceParent;

    public NewArray() {
    }

    public NewArray(TypeReference arrayName, ASTList<Expression> dimExpr) {
        setTypeReference(arrayName);
        setArguments(dimExpr);
        makeParentRoleValid();
    }

    public NewArray(TypeReference arrayName, int dimensions, ArrayInitializer initializer) {
        setTypeReference(arrayName);
        setDimensions(dimensions);
        setArrayInitializer(initializer);
        makeParentRoleValid();
    }

    protected NewArray(NewArray proto) {
        super(proto);
        if (proto.arrayInitializer != null)
            this.arrayInitializer = proto.arrayInitializer.deepClone();
        this.dimensions = proto.dimensions;
        makeParentRoleValid();
    }

    public NewArray deepClone() {
        return new NewArray(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.arrayInitializer != null)
            this.arrayInitializer.setExpressionContainer(this);
    }

    public SourceElement getLastElement() {
        if (this.arrayInitializer != null)
            return this.arrayInitializer.getLastElement();
        return this;
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.children != null) {
            int index = this.children.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        if (this.typeReference == child)
            return 1;
        if (this.arrayInitializer == child)
            return 3;
        return -1;
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.expressionParent != null)
            return this.expressionParent;
        return this.referenceParent;
    }

    public int getArity() {
        return 0;
    }

    public int getPrecedence() {
        return 0;
    }

    public int getNotation() {
        return 0;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.referenceParent;
    }

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.referenceParent = path;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.expressionParent;
    }

    public void setExpressionContainer(ExpressionContainer parent) {
        this.expressionParent = parent;
    }

    public int getDimensions() {
        return this.dimensions;
    }

    public void setDimensions(int dim) {
        this.dimensions = dim;
    }

    public ArrayInitializer getArrayInitializer() {
        return this.arrayInitializer;
    }

    public void setArrayInitializer(ArrayInitializer init) {
        this.arrayInitializer = init;
    }

    public int getChildCount() {
        int result = 0;
        if (this.typeReference != null)
            result++;
        if (this.children != null)
            result += this.children.size();
        if (this.arrayInitializer != null)
            result++;
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
        if (this.arrayInitializer != null &&
                index == 0)
            return this.arrayInitializer;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getExpressionCount() {
        int result = 0;
        if (this.children != null)
            result += this.children.size();
        if (this.arrayInitializer != null)
            result++;
        return result;
    }

    public Expression getExpressionAt(int index) {
        if (this.children != null) {
            int len = this.children.size();
            if (len > index)
                return this.children.get(index);
            index -= len;
        }
        if (this.arrayInitializer != null &&
                index == 0)
            return this.arrayInitializer;
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
        if (this.arrayInitializer == p) {
            ArrayInitializer r = (ArrayInitializer) q;
            this.arrayInitializer = r;
            if (r != null)
                r.setExpressionContainer(this);
            return true;
        }
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitNewArray(this);
    }
}
