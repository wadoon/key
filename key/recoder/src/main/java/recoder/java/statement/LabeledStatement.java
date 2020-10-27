package recoder.java.statement;

import recoder.java.*;

public class LabeledStatement extends JavaStatement implements StatementContainer, NamedProgramElement {
    private static final long serialVersionUID = -4621689270408033058L;

    protected Identifier name;

    protected Statement body;

    public LabeledStatement() {
    }

    public LabeledStatement(Identifier id) {
        setIdentifier(id);
        setBody(getFactory().createEmptyStatement());
        makeParentRoleValid();
    }

    public LabeledStatement(Identifier id, Statement statement) {
        setIdentifier(id);
        setBody(statement);
        makeParentRoleValid();
    }

    protected LabeledStatement(LabeledStatement proto) {
        super(proto);
        if (proto.name != null)
            this.name = proto.name.deepClone();
        if (proto.body != null)
            this.body = proto.body.deepClone();
        makeParentRoleValid();
    }

    public LabeledStatement deepClone() {
        return new LabeledStatement(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.name != null)
            this.name.setParent(this);
        if (this.body != null)
            this.body.setStatementContainer(this);
    }

    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    public SourceElement getLastElement() {
        return this.body.getLastElement();
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.name == p) {
            Identifier r = (Identifier) q;
            this.name = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        if (this.body == p) {
            Statement r = (Statement) q;
            this.body = r;
            if (r != null)
                r.setStatementContainer(this);
            return true;
        }
        return false;
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

    public Statement getBody() {
        return this.body;
    }

    public void setBody(Statement s) {
        this.body = s;
    }

    public int getChildCount() {
        int result = 0;
        if (this.name != null)
            result++;
        if (this.body != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.name != null) {
            if (index == 0)
                return this.name;
            index--;
        }
        if (this.body != null) {
            if (index == 0)
                return this.body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.name == child)
            return 0;
        if (this.body == child)
            return 1;
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

    public void accept(SourceVisitor v) {
        v.visitLabeledStatement(this);
    }
}
