package recoder.java.reference;

import recoder.java.*;

public class ArrayLengthReference extends JavaNonTerminalProgramElement implements Reference, Expression, ReferenceSuffix {
    private static final long serialVersionUID = 1267866126524827730L;

    protected ExpressionContainer expressionParent;

    protected ReferencePrefix prefix;

    public ArrayLengthReference() {
    }

    public ArrayLengthReference(ReferencePrefix prefix) {
        setReferencePrefix(prefix);
        makeParentRoleValid();
    }

    protected ArrayLengthReference(ArrayLengthReference proto) {
        super(proto);
        if (proto.prefix != null)
            this.prefix = (ReferencePrefix) proto.prefix.deepClone();
        makeParentRoleValid();
    }

    public ArrayLengthReference deepClone() {
        return new ArrayLengthReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.prefix != null)
            this.prefix.setReferenceSuffix(this);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.expressionParent;
    }

    public int getChildCount() {
        return (this.prefix != null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.prefix != null && index == 0)
            return this.prefix;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.prefix == child)
            return 0;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.prefix == p) {
            ReferencePrefix r = (ReferencePrefix) q;
            this.prefix = r;
            if (r != null)
                r.setReferenceSuffix(this);
            return true;
        }
        return false;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.prefix;
    }

    public void setReferencePrefix(ReferencePrefix prefix) {
        this.prefix = prefix;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.expressionParent;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.expressionParent = c;
    }

    public SourceElement getFirstElement() {
        return (this.prefix == null) ? this : this.prefix.getFirstElement();
    }

    public void accept(SourceVisitor v) {
        v.visitArrayLengthReference(this);
    }
}
