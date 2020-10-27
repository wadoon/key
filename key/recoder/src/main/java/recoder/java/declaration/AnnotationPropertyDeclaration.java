package recoder.java.declaration;

import recoder.abstraction.AnnotationProperty;
import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

public class AnnotationPropertyDeclaration extends MethodDeclaration implements AnnotationProperty, ExpressionContainer {
    private static final long serialVersionUID = -1319877992238107401L;

    protected Expression defaultValue;

    public AnnotationPropertyDeclaration() {
        makeParentRoleValid();
    }

    public AnnotationPropertyDeclaration(ASTList<DeclarationSpecifier> modifiers, TypeReference returnType, Identifier name, Expression defaultValue) {
        super(modifiers, returnType, name, null, null);
        this.defaultValue = defaultValue;
        makeParentRoleValid();
    }

    protected AnnotationPropertyDeclaration(AnnotationPropertyDeclaration proto) {
        super(proto);
        if (proto.defaultValue != null) {
            this.defaultValue = proto.defaultValue.deepClone();
            this.defaultValue.setExpressionContainer(this);
        }
    }

    public Object getDefaultValue() {
        return AnnotationElementValuePair.expressionToJavaObject(this.defaultValue);
    }

    public void setDefaultValue(Expression e) {
        this.defaultValue = e;
    }

    public Expression getDefaultValueExpression() {
        return this.defaultValue;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.defaultValue != null)
            this.defaultValue.setExpressionContainer(this);
    }

    public int getExpressionCount() {
        return (this.defaultValue == null) ? 0 : 1;
    }

    public Expression getExpressionAt(int index) {
        if (index == 0 && this.defaultValue != null)
            return this.defaultValue;
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public void accept(SourceVisitor v) {
        v.visitAnnotationPropertyDeclaration(this);
    }

    public AnnotationPropertyDeclaration deepClone() {
        return new AnnotationPropertyDeclaration(this);
    }

    public ProgramElement getChildAt(int index) {
        if (index == super.getChildCount() && this.defaultValue != null)
            return this.defaultValue;
        return super.getChildAt(index);
    }

    public int getChildCount() {
        return super.getChildCount() + ((this.defaultValue == null) ? 0 : 1);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (child == this.defaultValue)
            return 8;
        return super.getChildPositionCode(child);
    }

    public boolean isPrivate() {
        return false;
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPublic() {
        return true;
    }

    public boolean isVarArgMethod() {
        return false;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (p == this.defaultValue) {
            Expression r = (Expression) q;
            this.defaultValue = r;
            if (r != null)
                r.setExpressionContainer(this);
            return true;
        }
        return super.replaceChild(p, q);
    }
}
