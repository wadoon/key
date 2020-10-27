package recoder.java.declaration;

import recoder.abstraction.ClassType;
import recoder.abstraction.Field;
import recoder.abstraction.Member;
import recoder.convenience.Naming;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.SourceVisitor;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

import java.util.List;

public class FieldSpecification extends VariableSpecification implements Field {
    private static final long serialVersionUID = -8228158502939901347L;

    public FieldSpecification() {
    }

    public FieldSpecification(Identifier name) {
        super(name);
    }

    public FieldSpecification(Identifier name, Expression init) {
        super(name, init);
    }

    public FieldSpecification(Identifier name, int dimensions, Expression init) {
        super(name, dimensions, init);
    }

    protected FieldSpecification(FieldSpecification proto) {
        super(proto);
    }

    private static void updateModel() {
        factory.getServiceConfiguration().getChangeHistory().updateModel();
    }

    public FieldSpecification deepClone() {
        return new FieldSpecification(this);
    }

    public void setParent(VariableDeclaration parent) {
        setParent((FieldDeclaration) parent);
    }

    public void setParent(FieldDeclaration parent) {
        super.setParent(parent);
    }

    public boolean isPrivate() {
        return this.parent.isPrivate();
    }

    public boolean isProtected() {
        return this.parent.isProtected();
    }

    public boolean isPublic() {
        return this.parent.isPublic();
    }

    public boolean isStatic() {
        return this.parent.isStatic();
    }

    public boolean isTransient() {
        return this.parent.isTransient();
    }

    public boolean isVolatile() {
        return this.parent.isVolatile();
    }

    public ClassType getContainingClassType() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        return this.service.getContainingClassType(this);
    }

    public String getFullName() {
        return Naming.getFullName(this);
    }

    public void accept(SourceVisitor v) {
        v.visitFieldSpecification(this);
    }

    public List<AnnotationUseSpecification> getAnnotations() {
        return this.parent.getAnnotations();
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        return getParent().getTypeReference().getTypeArguments();
    }
}
