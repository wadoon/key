package recoder.java.reference;

import recoder.java.*;
import recoder.java.declaration.*;
import recoder.list.generic.ASTList;

public class EnumConstructorReference extends JavaNonTerminalProgramElement implements ConstructorReference, TypeDeclarationContainer {
    private static final long serialVersionUID = 346152574064180781L;

    protected ClassDeclaration classDeclaration;

    protected ASTList<Expression> args;

    protected EnumConstantSpecification parent;

    public EnumConstructorReference() {
    }

    public EnumConstructorReference(ASTList<Expression> args, ClassDeclaration anonymousClass) {
        this.args = args;
        this.classDeclaration = anonymousClass;
        makeParentRoleValid();
    }

    protected EnumConstructorReference(EnumConstructorReference proto) {
        super(proto);
        if (proto.classDeclaration != null)
            this.classDeclaration = proto.classDeclaration.deepClone();
        if (proto.args != null)
            this.args = proto.args.deepClone();
    }

    public void accept(SourceVisitor v) {
        v.visitEnumConstructorReference(this);
    }

    public EnumConstructorReference deepClone() {
        return new EnumConstructorReference(this);
    }

    public StatementContainer getStatementContainer() {
        return null;
    }

    public void setStatementContainer(StatementContainer c) {
        throw new UnsupportedOperationException();
    }

    public int getTypeDeclarationCount() {
        return (this.classDeclaration == null) ? 0 : 1;
    }

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (this.classDeclaration != null && index == 0)
            return this.classDeclaration;
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public ProgramElement getChildAt(int index) {
        if (this.args != null) {
            int l = this.args.size();
            if (index < l)
                return this.args.get(index);
            index -= l;
        }
        if (this.classDeclaration != null) {
            if (index == 0)
                return this.classDeclaration;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildCount() {
        return getTypeDeclarationCount() + ((this.args == null) ? 0 : this.args.size());
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.classDeclaration != null)
            this.classDeclaration.setParent(this);
        if (this.args != null)
            for (int i = 0, max = this.args.size(); i < max; i++) {
                Expression e = this.args.get(i);
                e.setExpressionContainer(this);
            }
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (p == this.classDeclaration) {
            this.classDeclaration = (ClassDeclaration) q;
            if (q != null)
                this.classDeclaration.setParent(this);
            return true;
        }
        int idx;
        if (this.args != null && (idx = this.args.indexOf(p)) != -1) {
            if (q == null) {
                this.args.remove(idx);
            } else {
                Expression s = (Expression) q;
                this.args.set(idx, s);
                s.setExpressionContainer(this);
            }
            return true;
        }
        return false;
    }

    public int getChildPositionCode(ProgramElement child) {
        if (child == this.classDeclaration)
            return 0;
        if (this.args != null) {
            int idx = this.args.indexOf(child);
            if (idx != -1)
                return idx << 4 | 0x1;
        }
        return -1;
    }

    public final ClassDeclaration getClassDeclaration() {
        return this.classDeclaration;
    }

    public final void setClassDeclaration(ClassDeclaration classDeclaration) {
        this.classDeclaration = classDeclaration;
    }

    public ASTList<Expression> getArguments() {
        return this.args;
    }

    public void setArguments(ASTList<Expression> list) {
        this.args = list;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public void setParent(EnumConstantSpecification parent) {
        this.parent = parent;
    }

    public int getExpressionCount() {
        return (this.args == null) ? 0 : this.args.size();
    }

    public Expression getExpressionAt(int index) {
        if (this.args == null)
            throw new ArrayIndexOutOfBoundsException(index);
        return this.args.get(index);
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        return null;
    }

    public ProgramElement getFirstElement() {
        if (this.args != null && this.args.size() > 0)
            return this.args.get(0);
        return this;
    }

    public ProgramElement getLastElement() {
        if (this.classDeclaration != null)
            return this.classDeclaration;
        if (this.args != null && this.args.size() > 0)
            return this.args.get(this.args.size() - 1);
        return this;
    }
}
