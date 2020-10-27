package recoder.java.statement;

import recoder.java.Expression;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;

public class While extends LoopStatement {
    private static final long serialVersionUID = -8497002453485096424L;

    public While() {
    }

    public While(Expression guard) {
        setGuard(guard);
        makeParentRoleValid();
    }

    public While(Expression guard, Statement body) {
        super(body);
        setGuard(guard);
        makeParentRoleValid();
    }

    protected While(While proto) {
        super(proto);
        makeParentRoleValid();
    }

    public While deepClone() {
        return new While(this);
    }

    public SourceElement getLastElement() {
        return (this.body != null) ? this.body.getLastElement() : this;
    }

    public boolean isExitCondition() {
        return false;
    }

    public boolean isCheckedBeforeIteration() {
        return true;
    }

    public void accept(SourceVisitor v) {
        v.visitWhile(this);
    }
}
