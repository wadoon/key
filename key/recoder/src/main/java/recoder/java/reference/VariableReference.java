package recoder.java.reference;

import recoder.java.*;

public class VariableReference extends JavaNonTerminalProgramElement implements NameReference, Expression, ReferencePrefix {
    private static final long serialVersionUID = 3652444943086603166L;

    protected ReferenceSuffix accessParent;

    protected ExpressionContainer parent;

    protected Identifier name;

    public VariableReference() {
    }

    public VariableReference(Identifier id) {
        setIdentifier(id);
        makeParentRoleValid();
    }

    protected VariableReference(VariableReference proto) {
        super(proto);
        if (proto.name != null)
            this.name = proto.name.deepClone();
        makeParentRoleValid();
    }

    public VariableReference deepClone() {
        return new VariableReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.name != null)
            this.name.setParent(this);
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.accessParent != null)
            return this.accessParent;
        return this.parent;
    }

    public int getChildCount() {
        return (this.name != null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.name != null &&
                index == 0)
            return this.name;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.name == child)
            return 0;
        return -1;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.accessParent;
    }

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.accessParent = path;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.name == p) {
            Identifier r = (Identifier) q;
            this.name = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        return false;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.parent;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.parent = c;
    }

    public final String getName() {
        return (this.name == null) ? null : this.name.getText();
    }

    public Identifier getIdentifier() {
        return this.name;
    }

    public void setIdentifier(Identifier id) {
        this.name = id;
    }

    public SourceElement getFirstElement() {
        return this.name;
    }

    public void accept(SourceVisitor v) {
        v.visitVariableReference(this);
    }
}
