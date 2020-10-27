package recoder.java.statement;

import recoder.java.Expression;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;

public class Do extends LoopStatement {
    private static final long serialVersionUID = -1933906789623152123L;

    public Do() {
    }

    public Do(Expression guard) {
        setGuard(guard);
        makeParentRoleValid();
    }

    public Do(Expression guard, Statement body) {
        super(body);
        setGuard(guard);
        makeParentRoleValid();
    }

    protected Do(Do proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Do deepClone() {
        return new Do(this);
    }

    public SourceElement getLastElement() {
        return this;
    }

    public boolean isExitCondition() {
        return true;
    }

    public boolean isCheckedBeforeIteration() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitDo(this);
    }
}
