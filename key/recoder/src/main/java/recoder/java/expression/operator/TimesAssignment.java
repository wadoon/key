package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class TimesAssignment extends Assignment {
    private static final long serialVersionUID = -1978899655527666905L;

    public TimesAssignment() {
    }

    public TimesAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected TimesAssignment(TimesAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public TimesAssignment deepClone() {
        return new TimesAssignment(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 13;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitTimesAssignment(this);
    }
}
