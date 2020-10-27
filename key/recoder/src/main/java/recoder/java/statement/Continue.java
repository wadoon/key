package recoder.java.statement;

import recoder.java.Identifier;
import recoder.java.SourceVisitor;

public class Continue extends LabelJumpStatement {
    private static final long serialVersionUID = 8896520115861515813L;

    public Continue() {
    }

    public Continue(Identifier label) {
        super(label);
        makeParentRoleValid();
    }

    protected Continue(Continue proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Continue deepClone() {
        return new Continue(this);
    }

    public void accept(SourceVisitor v) {
        v.visitContinue(this);
    }
}
