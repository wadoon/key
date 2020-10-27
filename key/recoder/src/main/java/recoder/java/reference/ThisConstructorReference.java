package recoder.java.reference;

import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.list.generic.ASTList;

public class ThisConstructorReference extends SpecialConstructorReference {
    private static final long serialVersionUID = -4669357517439005903L;

    public ThisConstructorReference() {
        makeParentRoleValid();
    }

    public ThisConstructorReference(ASTList<Expression> arguments) {
        super(arguments);
        makeParentRoleValid();
    }

    protected ThisConstructorReference(ThisConstructorReference proto) {
        super(proto);
        makeParentRoleValid();
    }

    public ThisConstructorReference deepClone() {
        return new ThisConstructorReference(this);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.arguments != null) {
            int index = this.arguments.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        return -1;
    }

    public void accept(SourceVisitor v) {
        v.visitThisConstructorReference(this);
    }
}
