package recoder.java.reference;

import recoder.java.*;
import recoder.java.declaration.AnnotationElementValuePair;

public class AnnotationPropertyReference extends JavaNonTerminalProgramElement implements MemberReference {
    private static final long serialVersionUID = 5822661522219760793L;

    protected Identifier ident;

    protected AnnotationElementValuePair parent;

    public AnnotationPropertyReference() {
    }

    public AnnotationPropertyReference(Identifier ident) {
        this.ident = ident;
        makeParentRoleValid();
    }

    public AnnotationPropertyReference(AnnotationPropertyReference proto) {
        super(proto);
        this.ident = proto.ident.deepClone();
        makeParentRoleValid();
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public AnnotationElementValuePair getParent() {
        return this.parent;
    }

    public void setParent(AnnotationElementValuePair parent) {
        this.parent = parent;
    }

    public void accept(SourceVisitor v) {
        v.visitAnnotationPropertyReference(this);
    }

    public AnnotationPropertyReference deepClone() {
        return new AnnotationPropertyReference(this);
    }

    public int getChildCount() {
        return (this.ident == null) ? 0 : 1;
    }

    public ProgramElement getChildAt(int index) {
        if (this.ident != null && index == 0)
            return this.ident;
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public int getChildPositionCode(ProgramElement child) {
        return (child == this.ident) ? 0 : -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == this.ident) {
            this.ident = (Identifier) q;
            if (this.ident != null)
                this.ident.setParent(this);
            return true;
        }
        return false;
    }

    public Identifier getIdentifier() {
        return this.ident;
    }

    public void setIdentifier(Identifier ident) {
        this.ident = ident;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.ident != null)
            this.ident.setParent(this);
    }

    public int getExpressionCount() {
        return 0;
    }

    public Expression getExpressionAt(int index) {
        throw new IndexOutOfBoundsException();
    }

    public SourceElement getFirstElement() {
        return this.ident;
    }

    public SourceElement getLastElement() {
        return this.ident;
    }
}
