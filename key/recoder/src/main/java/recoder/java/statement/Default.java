package recoder.java.statement;

import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.list.generic.ASTList;

public class Default extends Branch {
    private static final long serialVersionUID = 7895466623038779294L;

    protected ASTList<Statement> body;

    public Default() {
    }

    public Default(ASTList<Statement> body) {
        setBody(body);
        makeParentRoleValid();
    }

    protected Default(Default proto) {
        super(proto);
        if (proto.body != null)
            this.body = proto.body.deepClone();
        makeParentRoleValid();
    }

    public Default deepClone() {
        return new Default(this);
    }

    public void setParent(Switch parent) {
        this.parent = parent;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.body != null)
            for (int i = 0; i < this.body.size(); i++)
                this.body.get(i).setStatementContainer(this);
    }

    public int getChildCount() {
        int result = 0;
        if (this.body != null)
            result += this.body.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.body != null) {
            int len = this.body.size();
            if (len > index)
                return this.body.get(index);
            index -= len;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.body != null) {
            int index = this.body.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.body == null) ? 0 : this.body.size();
        for (int i = 0; i < count; i++) {
            if (this.body.get(i) == p) {
                if (q == null) {
                    this.body.remove(i);
                } else {
                    Statement r = (Statement) q;
                    this.body.set(i, r);
                    r.setStatementContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    public int getStatementCount() {
        return (this.body != null) ? this.body.size() : 0;
    }

    public Statement getStatementAt(int index) {
        if (this.body != null)
            return this.body.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public ASTList<Statement> getBody() {
        return this.body;
    }

    public void setBody(ASTList<Statement> list) {
        this.body = list;
    }

    public void accept(SourceVisitor v) {
        v.visitDefault(this);
    }

    public SourceElement getLastElement() {
        if (this.body == null || this.body.size() == 0)
            return this;
        return this.body.get(this.body.size() - 1).getLastElement();
    }
}
