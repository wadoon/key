package recoder.java.statement;

import recoder.java.*;
import recoder.list.generic.ASTList;

public class Try extends BranchStatement implements StatementContainer {
    private static final long serialVersionUID = -6939974882487466260L;

    protected StatementBlock body;

    protected ASTList<Branch> branches;

    public Try() {
    }

    public Try(StatementBlock body) {
        setBody(body);
        makeParentRoleValid();
    }

    public Try(StatementBlock body, ASTList<Branch> branches) {
        setBranchList(branches);
        setBody(body);
        makeParentRoleValid();
    }

    protected Try(Try proto) {
        super(proto);
        if (proto.body != null)
            this.body = proto.body.deepClone();
        if (proto.branches != null)
            this.branches = proto.branches.deepClone();
        makeParentRoleValid();
    }

    public Try deepClone() {
        return new Try(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.body != null)
            this.body.setStatementContainer(this);
        if (this.branches != null)
            for (int i = this.branches.size() - 1; i >= 0; i--) {
                Branch b = this.branches.get(i);
                if (b instanceof Catch) {
                    ((Catch) b).setParent(this);
                } else {
                    ((Finally) b).setParent(this);
                }
            }
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    public int getChildCount() {
        int result = 0;
        if (this.body != null)
            result++;
        if (this.branches != null)
            result += this.branches.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.body != null) {
            if (index == 0)
                return this.body;
            index--;
        }
        if (this.branches != null)
            return this.branches.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.body == child)
            return 0;
        if (this.branches != null) {
            int index = this.branches.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x1;
        }
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.body == p) {
            StatementBlock r = (StatementBlock) q;
            this.body = r;
            if (r != null)
                r.setStatementContainer(this);
            return true;
        }
        int count = (this.branches == null) ? 0 : this.branches.size();
        for (int i = 0; i < count; i++) {
            if (this.branches.get(i) == p) {
                if (q == null) {
                    this.branches.remove(i);
                } else if (q instanceof Catch) {
                    this.branches.set(i, q);
                    ((Catch) q).setParent(this);
                } else {
                    this.branches.set(i, q);
                    ((Finally) q).setParent(this);
                }
                return true;
            }
        }
        return false;
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

    public ASTList<Branch> getBranchList() {
        return this.branches;
    }

    public void setBranchList(ASTList<Branch> branches) {
        this.branches = branches;
    }

    public int getBranchCount() {
        return (this.branches != null) ? this.branches.size() : 0;
    }

    public Branch getBranchAt(int index) {
        if (this.branches != null)
            return this.branches.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public void accept(SourceVisitor v) {
        v.visitTry(this);
    }
}
