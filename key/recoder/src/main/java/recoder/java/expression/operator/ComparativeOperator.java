package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.expression.Operator;

public abstract class ComparativeOperator extends Operator {
    public ComparativeOperator() {
    }

    public ComparativeOperator(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    protected ComparativeOperator(ComparativeOperator proto) {
        super(proto);
        makeParentRoleValid();
    }

    public int getArity() {
        return 2;
    }

    public int getNotation() {
        return 1;
    }
}
