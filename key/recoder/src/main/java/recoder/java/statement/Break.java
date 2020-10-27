package recoder.java.statement;

import recoder.java.Identifier;
import recoder.java.SourceVisitor;

public class Break extends LabelJumpStatement {
    private static final long serialVersionUID = 6926617993568300612L;

    public Break() {
        makeParentRoleValid();
    }

    public Break(Identifier label) {
        super(label);
        makeParentRoleValid();
    }

    protected Break(Break proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Break deepClone() {
        return new Break(this);
    }

    public void accept(SourceVisitor v) {
        v.visitBreak(this);
    }
}
