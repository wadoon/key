package recoder.java.reference;

import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.list.generic.ASTList;

public class SuperConstructorReference extends SpecialConstructorReference implements ReferenceSuffix {
    private static final long serialVersionUID = 5432343818938120448L;

    protected ReferencePrefix accessPath;

    protected ASTList<TypeArgumentDeclaration> typeArguments;

    public SuperConstructorReference() {
        makeParentRoleValid();
    }

    public SuperConstructorReference(ASTList<Expression> arguments) {
        super(arguments);
        makeParentRoleValid();
    }

    public SuperConstructorReference(ReferencePrefix path, ASTList<Expression> arguments) {
        super(arguments);
        setReferencePrefix(path);
        makeParentRoleValid();
    }

    protected SuperConstructorReference(SuperConstructorReference proto) {
        super(proto);
        if (proto.accessPath != null)
            this.accessPath = (ReferencePrefix) proto.accessPath.deepClone();
        makeParentRoleValid();
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.accessPath != null)
            this.accessPath.setReferenceSuffix(this);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.accessPath == child)
            return 0;
        if (this.arguments != null) {
            int index = this.arguments.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x1;
        }
        return -1;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.accessPath;
    }

    public void setReferencePrefix(ReferencePrefix qualifier) {
        this.accessPath = qualifier;
    }

    public SuperConstructorReference deepClone() {
        return new SuperConstructorReference(this);
    }

    public SourceElement getFirstElement() {
        return (this.accessPath == null) ? this : this.accessPath.getFirstElement();
    }

    public void accept(SourceVisitor v) {
        v.visitSuperConstructorReference(this);
    }
}
