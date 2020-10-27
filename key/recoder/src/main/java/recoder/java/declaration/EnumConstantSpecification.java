package recoder.java.declaration;

import recoder.ModelException;
import recoder.abstraction.EnumConstant;
import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.reference.EnumConstructorReference;
import recoder.list.generic.ASTList;

public class EnumConstantSpecification extends FieldSpecification implements EnumConstant {
    private static final long serialVersionUID = -40018491975119655L;

    protected EnumConstructorReference ref;

    public EnumConstantSpecification() {
    }

    public EnumConstantSpecification(Identifier name) {
        super(name);
    }

    public EnumConstantSpecification(Identifier name, EnumConstructorReference ref) {
        super(name);
        this.ref = ref;
        makeParentRoleValid();
    }

    public EnumConstantSpecification(EnumConstantSpecification proto) {
        super(proto);
        if (proto.ref != null)
            this.ref = proto.ref.deepClone();
    }

    public void accept(SourceVisitor v) {
        v.visitEnumConstantSpecification(this);
    }

    public EnumConstantSpecification deepClone() {
        return new EnumConstantSpecification(this);
    }

    public EnumConstantDeclaration getParent() {
        return (EnumConstantDeclaration) this.parent;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.ref != null)
            this.ref.setParent(this);
    }

    public int getChildCount() {
        return super.getChildCount() + ((this.ref == null) ? 0 : 1);
    }

    public ProgramElement getChildAt(int pos) {
        if (pos == super.getChildCount() && this.ref != null)
            return this.ref;
        return super.getChildAt(pos);
    }

    public EnumConstructorReference getConstructorReference() {
        return this.ref;
    }

    public void setConstructorReference(EnumConstructorReference ref) {
        this.ref = ref;
    }

    public void validate() throws ModelException {
        super.validate();
        if (this.ref == null)
            throw new ModelException("EnumConstructorReference not set in " + getFullName());
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        return null;
    }
}
