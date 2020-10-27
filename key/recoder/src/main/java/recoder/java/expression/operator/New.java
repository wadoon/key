package recoder.java.expression.operator;

import recoder.java.*;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.TypeDeclarationContainer;
import recoder.java.expression.ExpressionStatement;
import recoder.java.reference.ConstructorReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

public class New extends TypeOperator implements ConstructorReference, ExpressionStatement, ReferencePrefix, ReferenceSuffix, TypeDeclarationContainer {
    private static final long serialVersionUID = -4983184360698832328L;

    protected ClassDeclaration anonymousClass;

    protected ReferencePrefix accessPath;

    protected ReferenceSuffix referenceParent;

    protected StatementContainer statementParent;

    public New() {
    }

    public New(ReferencePrefix accessPath, TypeReference constructorName, ASTList<Expression> arguments) {
        setReferencePrefix(accessPath);
        setTypeReference(constructorName);
        setArguments(arguments);
        makeParentRoleValid();
    }

    public New(ReferencePrefix accessPath, TypeReference constructorName, ASTList<Expression> arguments, ClassDeclaration anonymousClass) {
        this(accessPath, constructorName, arguments);
        setClassDeclaration(anonymousClass);
        makeParentRoleValid();
    }

    protected New(New proto) {
        super(proto);
        if (proto.anonymousClass != null)
            this.anonymousClass = proto.anonymousClass.deepClone();
        if (proto.accessPath != null)
            this.accessPath = (ReferencePrefix) proto.accessPath.deepClone();
        makeParentRoleValid();
    }

    public New deepClone() {
        return new New(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.children != null)
            for (int i = this.children.size() - 1; i >= 0; i--)
                this.children.get(i).setExpressionContainer(this);
        if (this.accessPath != null)
            this.accessPath.setReferenceSuffix(this);
        if (this.anonymousClass != null)
            this.anonymousClass.setParent(this);
    }

    public SourceElement getFirstElement() {
        return (this.accessPath != null) ? this.accessPath.getFirstElement() : this;
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.statementParent != null)
            return this.statementParent;
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

    public StatementContainer getStatementContainer() {
        return this.statementParent;
    }

    public void setStatementContainer(StatementContainer parent) {
        this.statementParent = parent;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.expressionParent;
    }

    public void setExpressionContainer(ExpressionContainer parent) {
        this.expressionParent = parent;
    }

    public ClassDeclaration getClassDeclaration() {
        return this.anonymousClass;
    }

    public void setClassDeclaration(ClassDeclaration decl) {
        this.anonymousClass = decl;
    }

    public int getTypeDeclarationCount() {
        return (this.anonymousClass != null) ? 1 : 0;
    }

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (this.anonymousClass != null && index == 0)
            return this.anonymousClass;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildCount() {
        int result = 0;
        if (this.accessPath != null)
            result++;
        if (this.typeReference != null)
            result++;
        if (this.children != null)
            result += this.children.size();
        if (this.anonymousClass != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.accessPath != null) {
            if (index == 0)
                return this.accessPath;
            index--;
        }
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
        if (this.anonymousClass != null) {
            if (index == 0)
                return this.anonymousClass;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.children != null) {
            int index = this.children.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        if (this.typeReference == child)
            return 1;
        if (this.accessPath == child)
            return 2;
        if (this.anonymousClass == child)
            return 3;
        return -1;
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
        if (this.accessPath == p) {
            ReferencePrefix r = (ReferencePrefix) q;
            this.accessPath = r;
            if (r != null)
                r.setReferenceSuffix(this);
            return true;
        }
        if (this.anonymousClass == p) {
            ClassDeclaration r = (ClassDeclaration) q;
            this.anonymousClass = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        return false;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.accessPath;
    }

    public void setReferencePrefix(ReferencePrefix x) {
        this.accessPath = x;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.referenceParent;
    }

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.referenceParent = path;
    }

    public ASTList<Expression> getArguments() {
        return this.children;
    }

    public void setArguments(ASTList<Expression> list) {
        this.children = list;
    }

    public void accept(SourceVisitor v) {
        v.visitNew(this);
    }
}
