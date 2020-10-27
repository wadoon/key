package recoder.java.declaration;

import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class Throws extends JavaNonTerminalProgramElement implements TypeReferenceContainer {
    private static final long serialVersionUID = 7556905452727718279L;

    protected MethodDeclaration parent;

    protected ASTList<TypeReference> exceptions;

    public Throws() {
    }

    public Throws(TypeReference exception) {
        this.exceptions = (ASTList<TypeReference>) new ASTArrayList(1);
        this.exceptions.add(exception);
        makeParentRoleValid();
    }

    public Throws(ASTList<TypeReference> list) {
        this.exceptions = list;
        makeParentRoleValid();
    }

    protected Throws(Throws proto) {
        super(proto);
        if (proto.exceptions != null)
            this.exceptions = proto.exceptions.deepClone();
        makeParentRoleValid();
    }

    public Throws deepClone() {
        return new Throws(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.exceptions != null)
            for (int i = this.exceptions.size() - 1; i >= 0; i--)
                this.exceptions.get(i).setParent(this);
    }

    public SourceElement getLastElement() {
        if (this.exceptions == null)
            return this;
        return this.exceptions.get(this.exceptions.size() - 1);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public int getChildCount() {
        int result = 0;
        if (this.exceptions != null)
            result += this.exceptions.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.exceptions != null)
            return this.exceptions.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.exceptions != null) {
            int index = this.exceptions.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.exceptions == null) ? 0 : this.exceptions.size();
        for (int i = 0; i < count; i++) {
            if (this.exceptions.get(i) == p) {
                if (q == null) {
                    this.exceptions.remove(i);
                } else {
                    TypeReference r = (TypeReference) q;
                    this.exceptions.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public MethodDeclaration getParent() {
        return this.parent;
    }

    public void setParent(MethodDeclaration decl) {
        this.parent = decl;
    }

    public ASTList<TypeReference> getExceptions() {
        return this.exceptions;
    }

    public void setExceptions(ASTList<TypeReference> list) {
        this.exceptions = list;
    }

    public int getTypeReferenceCount() {
        return (this.exceptions != null) ? this.exceptions.size() : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.exceptions != null)
            return this.exceptions.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public void accept(SourceVisitor v) {
        v.visitThrows(this);
    }
}
