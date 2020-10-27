package recoder.java.statement;

import recoder.java.*;

public class Finally extends Branch {
    private static final long serialVersionUID = -7603770274498242193L;

    protected StatementBlock body;

    public Finally() {
    }

    public Finally(StatementBlock body) {
        setBody(body);
        makeParentRoleValid();
    }

    protected Finally(Finally proto) {
        super(proto);
        if (proto.body != null)
            this.body = proto.body.deepClone();
        makeParentRoleValid();
    }

    public Finally deepClone() {
        return new Finally(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.body != null)
            this.body.setStatementContainer(this);
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
        return false;
    }

    public int getChildCount() {
        int result = 0;
        if (this.body != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.body != null) {
            if (index == 0)
                return this.body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.body == child)
            return 0;
        return -1;
    }

    public int getStatementCount() {
        return (this.body != null) ? 1 : 0;
    }

    public Statement getStatementAt(int index) {
        if (this.body != null && index == 0)
            return this.body;
        throw new ArrayIndexOutOfBoundsException();
    }

    public Statement getBody() {
        return this.body;
    }

    public void setBody(Statement statement) {
        this.body = (StatementBlock) statement;
    }

    public void setParent(Try parent) {
        this.parent = parent;
    }

    public SourceElement getLastElement() {
        return this.body;
    }

    public void accept(SourceVisitor v) {
        v.visitFinally(this);
    }
}
