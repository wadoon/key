package recoder.java.declaration;

import recoder.java.*;
import recoder.java.declaration.modifier.Static;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class ClassInitializer extends JavaDeclaration implements MemberDeclaration, StatementContainer {
    private static final long serialVersionUID = 7172264701196251395L;

    protected TypeDeclaration parent;

    protected StatementBlock body;

    public ClassInitializer() {
    }

    public ClassInitializer(StatementBlock body) {
        setBody(body);
        makeParentRoleValid();
    }

    public ClassInitializer(Static modifier, StatementBlock body) {
        if (modifier != null) {
            ASTArrayList aSTArrayList = new ASTArrayList(1);
            aSTArrayList.add(modifier);
            setDeclarationSpecifiers((ASTList<DeclarationSpecifier>) aSTArrayList);
        }
        setBody(body);
        makeParentRoleValid();
    }

    protected ClassInitializer(ClassInitializer proto) {
        super(proto);
        if (proto.body != null)
            this.body = proto.body.deepClone();
        makeParentRoleValid();
    }

    public ClassInitializer deepClone() {
        return new ClassInitializer(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.body != null)
            this.body.setStatementContainer(this);
    }

    public SourceElement getFirstElement() {
        if (this.declarationSpecifiers != null && !this.declarationSpecifiers.isEmpty())
            return this.declarationSpecifiers.get(0);
        return this.body;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public StatementBlock getBody() {
        return this.body;
    }

    public void setBody(StatementBlock body) {
        this.body = body;
    }

    public int getStatementCount() {
        return (this.body != null) ? 1 : 0;
    }

    public Statement getStatementAt(int index) {
        if (this.body != null && index == 0)
            return this.body;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildCount() {
        int result = 0;
        if (this.declarationSpecifiers != null)
            result += this.declarationSpecifiers.size();
        if (this.body != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.declarationSpecifiers != null) {
            int len = this.declarationSpecifiers.size();
            if (len > index)
                return this.declarationSpecifiers.get(index);
            index -= len;
        }
        if (this.body != null &&
                index == 0)
            return this.body;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.declarationSpecifiers != null) {
            int index = this.declarationSpecifiers.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        if (this.body == child)
            return 1;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.declarationSpecifiers == null) ? 0 : this.declarationSpecifiers.size();
        for (int i = 0; i < count; i++) {
            if (this.declarationSpecifiers.get(i) == p) {
                if (q == null) {
                    this.declarationSpecifiers.remove(i);
                } else {
                    Static r = (Static) q;
                    this.declarationSpecifiers.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        if (this.body == p) {
            StatementBlock r = (StatementBlock) q;
            this.body = r;
            if (r != null)
                r.setStatementContainer(this);
            return true;
        }
        return false;
    }

    public TypeDeclaration getMemberParent() {
        return this.parent;
    }

    public void setMemberParent(TypeDeclaration t) {
        this.parent = t;
    }

    public boolean isBinary() {
        return false;
    }

    public boolean isPublic() {
        return false;
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPrivate() {
        return false;
    }

    public boolean isStrictFp() {
        return false;
    }

    public boolean isStatic() {
        return (this.declarationSpecifiers != null && !this.declarationSpecifiers.isEmpty());
    }

    public SourceElement getLastElement() {
        return this.body;
    }

    public void accept(SourceVisitor v) {
        v.visitClassInitializer(this);
    }
}
