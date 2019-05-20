
package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.statement.JavaStatement;

public class Assume extends JavaStatement implements ExpressionContainer {

    protected Expression condition;

    public Assume() {
    }

    public Assume(Expression cond) {
        if (cond == null) {
            throw new NullPointerException();
        }

        this.condition = cond;
        this.makeParentRoleValid();
    }

    protected Assume(Assume proto) {
        super(proto);
        if (proto.condition != null) {
            this.condition = proto.condition.deepClone();
        }

        this.makeParentRoleValid();
    }

    public Assume deepClone() {
        return new Assume(this);
    }

    public SourceElement getLastElement() {
        return this.condition.getLastElement();
    }

    public int getChildCount() {
        return 1;
    }

    public ProgramElement getChildAt(int index) {
        if (this.condition != null) {
            if (index == 0) {
                return this.condition;
            }

            --index;
        }

        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.condition == child) {
            return 0;
        } else {
            return -1;
        }
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.condition != null) {
            this.condition.setExpressionContainer(this);
        }
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        } else {
            Expression r;
            if (this.condition == p) {
                r = (Expression)q;
                this.condition = r;
                if (r != null) {
                    r.setExpressionContainer(this);
                }

                return true;
            } else {
                return false;
            }
        }
    }

    public int getExpressionCount() {
        int c = 0;
        if (this.condition != null) {
            ++c;
        }

        return c;
    }

    public Expression getExpressionAt(int index) {
        if (this.condition != null) {
            if (index == 0) {
                return this.condition;
            }

            --index;
        }

        throw new ArrayIndexOutOfBoundsException();
    }

    public Expression getCondition() {
        return this.condition;
    }

    public void setCondition(Expression expr) {
        this.condition = expr;
    }

    public void accept(SourceVisitor v) {
        // TODO: Check if we have to do anything
    }
}
