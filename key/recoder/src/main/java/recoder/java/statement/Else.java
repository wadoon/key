package recoder.java.statement;

import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;

public class Else extends Branch {
    private static final long serialVersionUID = 5468467558759778758L;

    protected Statement body;

    public Else() {
    }

    public Else(Statement body) {
        setBody(body);
        makeParentRoleValid();
    }

    protected Else(Else proto) {
        super(proto);
        if (proto.body != null)
            this.body = proto.body.deepClone();
        makeParentRoleValid();
    }

    public Else deepClone() {
        return new Else(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.body != null)
            this.body.setStatementContainer(this);
    }

    public SourceElement getLastElement() {
        return this.body.getLastElement();
    }

    public int getChildCount() {
        return (this.body != null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.body != null &&
                index == 0)
            return this.body;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.body == child)
            return 0;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.body == p) {
            Statement r = (Statement) q;
            this.body = r;
            if (r != null)
                r.setStatementContainer(this);
            return true;
        }
        return false;
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
        this.body = statement;
    }

    public void setParent(If parent) {
        this.parent = parent;
    }

    public void accept(SourceVisitor v) {
        v.visitElse(this);
    }
}
