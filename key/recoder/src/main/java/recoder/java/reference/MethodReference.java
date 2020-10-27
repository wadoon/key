package recoder.java.reference;

import recoder.java.*;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.expression.ExpressionStatement;
import recoder.list.generic.ASTList;

public class MethodReference extends JavaNonTerminalProgramElement implements MemberReference, ReferencePrefix, ReferenceSuffix, ExpressionStatement, TypeReferenceContainer, NameReference {
    private static final long serialVersionUID = -3016310919182753074L;

    protected ExpressionContainer expressionParent;

    protected StatementContainer statementParent;

    protected ReferenceSuffix qualifierParent;

    protected ReferencePrefix accessPath;

    protected Identifier name;

    protected ASTList<Expression> arguments;

    protected ASTList<TypeArgumentDeclaration> typeArguments;

    public MethodReference() {
    }

    public MethodReference(Identifier name) {
        setIdentifier(name);
        makeParentRoleValid();
    }

    public MethodReference(ReferencePrefix accessPath, Identifier name) {
        setReferencePrefix(accessPath);
        setIdentifier(name);
        makeParentRoleValid();
    }

    public MethodReference(Identifier name, ASTList<Expression> args) {
        setIdentifier(name);
        setArguments(args);
        makeParentRoleValid();
    }

    public MethodReference(ReferencePrefix accessPath, Identifier name, ASTList<Expression> args) {
        setReferencePrefix(accessPath);
        setIdentifier(name);
        setArguments(args);
        makeParentRoleValid();
    }

    public MethodReference(ReferencePrefix accessPath, Identifier name, ASTList<Expression> args, ASTList<TypeArgumentDeclaration> typeArgs) {
        setReferencePrefix(accessPath);
        setIdentifier(name);
        setArguments(args);
        setTypeArguments(typeArgs);
        makeParentRoleValid();
    }

    protected MethodReference(MethodReference proto) {
        super(proto);
        if (proto.accessPath != null)
            this.accessPath = (ReferencePrefix) proto.accessPath.deepClone();
        if (proto.name != null)
            this.name = proto.name.deepClone();
        if (proto.arguments != null)
            this.arguments = proto.arguments.deepClone();
        makeParentRoleValid();
    }

    public MethodReference deepClone() {
        return new MethodReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.accessPath != null)
            this.accessPath.setReferenceSuffix(this);
        if (this.name != null)
            this.name.setParent(this);
        if (this.arguments != null)
            for (int i = this.arguments.size() - 1; i >= 0; i--)
                this.arguments.get(i).setExpressionContainer(this);
        if (this.typeArguments != null)
            for (TypeArgumentDeclaration ta : this.typeArguments)
                ta.setParent(this);
    }

    public SourceElement getFirstElement() {
        return (this.accessPath == null) ? getChildAt(0).getFirstElement() : this.accessPath.getFirstElement();
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.statementParent != null)
            return this.statementParent;
        if (this.expressionParent != null)
            return this.expressionParent;
        return this.qualifierParent;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.accessPath;
    }

    public void setReferencePrefix(ReferencePrefix qualifier) {
        this.accessPath = qualifier;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.qualifierParent;
    }

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.qualifierParent = path;
        this.expressionParent = null;
        this.statementParent = null;
    }

    public StatementContainer getStatementContainer() {
        return this.statementParent;
    }

    public void setStatementContainer(StatementContainer parent) {
        this.statementParent = parent;
        this.expressionParent = null;
        this.qualifierParent = null;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.expressionParent;
    }

    public void setExpressionContainer(ExpressionContainer parent) {
        this.expressionParent = parent;
        this.statementParent = null;
        this.qualifierParent = null;
    }

    public int getChildCount() {
        int result = 0;
        if (this.accessPath != null)
            result++;
        if (this.name != null)
            result++;
        if (this.arguments != null)
            result += this.arguments.size();
        if (this.typeArguments != null)
            result += this.typeArguments.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.accessPath != null) {
            if (index == 0)
                return this.accessPath;
            index--;
        }
        if (this.name != null) {
            if (index == 0)
                return this.name;
            index--;
        }
        if (this.arguments != null) {
            int len = this.arguments.size();
            if (len > index)
                return this.arguments.get(index);
            index -= len;
        }
        if (this.typeArguments != null) {
            int len = this.typeArguments.size();
            if (len > index)
                return this.typeArguments.get(index);
            index -= len;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.accessPath == child)
            return 0;
        if (this.name == child)
            return 1;
        if (this.arguments != null) {
            int index = this.arguments.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x2;
        }
        if (this.typeArguments != null) {
            int index = this.typeArguments.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x3;
        }
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.accessPath == p) {
            ReferencePrefix r = (ReferencePrefix) q;
            this.accessPath = r;
            if (r != null)
                r.setReferenceSuffix(this);
            return true;
        }
        if (this.name == p) {
            Identifier r = (Identifier) q;
            this.name = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        int count = (this.arguments == null) ? 0 : this.arguments.size();
        for (int i = 0; i < count; i++) {
            if (this.arguments.get(i) == p) {
                if (q == null) {
                    this.arguments.remove(i);
                } else {
                    Expression r = (Expression) q;
                    this.arguments.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        if (this.typeArguments != null) {
            int idx = this.typeArguments.indexOf(p);
            if (idx != -1)
                if (q == null) {
                    this.typeArguments.remove(idx);
                } else {
                    TypeArgumentDeclaration tad = (TypeArgumentDeclaration) q;
                    this.typeArguments.set(idx, tad);
                    tad.setParent(this);
                }
        }
        return false;
    }

    public int getTypeReferenceCount() {
        return (this.accessPath instanceof TypeReference) ? 1 : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.accessPath instanceof TypeReference && index == 0)
            return (TypeReference) this.accessPath;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getExpressionCount() {
        int result = 0;
        if (this.accessPath instanceof Expression)
            result++;
        if (this.arguments != null)
            result += this.arguments.size();
        return result;
    }

    public Expression getExpressionAt(int index) {
        if (this.accessPath instanceof Expression) {
            if (index == 0)
                return (Expression) this.accessPath;
            index--;
        }
        if (this.arguments != null)
            return this.arguments.get(index);
        throw new ArrayIndexOutOfBoundsException();
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

    public ASTList<Expression> getArguments() {
        return this.arguments;
    }

    public void setArguments(ASTList<Expression> list) {
        this.arguments = list;
    }

    public void accept(SourceVisitor v) {
        v.visitMethodReference(this);
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        return this.typeArguments;
    }

    public void setTypeArguments(ASTList<TypeArgumentDeclaration> typeArguments) {
        this.typeArguments = typeArguments;
    }
}
