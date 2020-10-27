package recoder.java.statement;

import recoder.java.*;
import recoder.java.expression.ExpressionStatement;
import recoder.list.generic.ASTList;

public abstract class LoopStatement extends JavaStatement implements StatementContainer, ExpressionContainer {
    protected Expression guard;

    protected ASTList<LoopInitializer> inits;

    protected ASTList<Expression> updates;

    protected Statement body;

    public LoopStatement() {
    }

    public LoopStatement(Statement body) {
        setBody(body);
    }

    protected LoopStatement(LoopStatement proto) {
        super(proto);
        if (proto.guard != null)
            this.guard = proto.guard.deepClone();
        if (proto.inits != null)
            this.inits = proto.inits.deepClone();
        if (proto.updates != null)
            this.updates = proto.updates.deepClone();
        if (proto.body != null)
            this.body = proto.body.deepClone();
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.inits != null)
            for (int i = this.inits.size() - 1; i >= 0; i--) {
                LoopInitializer li = this.inits.get(i);
                if (li instanceof ExpressionStatement) {
                    ((ExpressionStatement) li).setExpressionContainer(this);
                } else {
                    li.setStatementContainer(this);
                }
            }
        if (this.guard != null)
            this.guard.setExpressionContainer(this);
        if (this.updates != null)
            for (int i = this.updates.size() - 1; i >= 0; i--)
                this.updates.get(i).setExpressionContainer(this);
        if (this.body != null)
            this.body.setStatementContainer(this);
    }

    public int getChildCount() {
        int result = 0;
        if (this.inits != null)
            result += this.inits.size();
        if (this.guard != null)
            result++;
        if (this.updates != null)
            result += this.updates.size();
        if (this.body != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.inits != null) {
            int len = this.inits.size();
            if (len > index)
                return this.inits.get(index);
            index -= len;
        }
        if (isCheckedBeforeIteration() &&
                this.guard != null) {
            if (index == 0)
                return this.guard;
            index--;
        }
        if (this.updates != null) {
            int len = this.updates.size();
            if (len > index)
                return this.updates.get(index);
            index -= len;
        }
        if (this.body != null) {
            if (index == 0)
                return this.body;
            index--;
        }
        if (!isCheckedBeforeIteration() &&
                this.guard != null) {
            if (index == 0)
                return this.guard;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.inits != null) {
            int index = this.inits.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        if (this.guard == child)
            return 1;
        if (this.updates != null) {
            int index = this.updates.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x2;
        }
        if (this.body == child)
            return 3;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.inits == null) ? 0 : this.inits.size();
        int i;
        for (i = 0; i < count; i++) {
            if (this.inits.get(i) == p) {
                if (q == null) {
                    this.inits.remove(i);
                } else {
                    LoopInitializer r = (LoopInitializer) q;
                    this.inits.set(i, r);
                    if (r instanceof ExpressionStatement) {
                        ((ExpressionStatement) r).setExpressionContainer(this);
                    } else {
                        r.setStatementContainer(this);
                    }
                }
                return true;
            }
        }
        if (this.guard == p) {
            Expression r = (Expression) q;
            this.guard = r;
            if (r != null)
                r.setExpressionContainer(this);
            return true;
        }
        count = (this.updates == null) ? 0 : this.updates.size();
        for (i = 0; i < count; i++) {
            if (this.updates.get(i) == p) {
                if (q == null) {
                    this.updates.remove(i);
                } else {
                    Expression r = (Expression) q;
                    this.updates.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
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

    public int getExpressionCount() {
        int result = 0;
        if (this.guard != null)
            result++;
        if (this.inits != null)
            for (int i = this.inits.size() - 1; i >= 0; i--) {
                if (this.inits.get(i) instanceof Expression)
                    result++;
            }
        if (this.updates != null)
            result += this.updates.size();
        return result;
    }

    public Expression getExpressionAt(int index) {
        if (this.guard != null) {
            if (index == 0)
                return this.guard;
            index--;
        }
        if (this.inits != null) {
            int s = this.inits.size();
            for (int i = 0; i < s && index >= 0; i++) {
                LoopInitializer ii = this.inits.get(i);
                if (ii instanceof Expression) {
                    if (index == 0)
                        return (Expression) ii;
                    index--;
                }
            }
        }
        if (this.updates != null)
            return this.updates.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public Expression getGuard() {
        return this.guard;
    }

    public void setGuard(Expression expr) {
        this.guard = expr;
    }

    public Statement getBody() {
        return this.body;
    }

    public void setBody(Statement statement) {
        this.body = statement;
    }

    public int getStatementCount() {
        return (this.body != null) ? 1 : 0;
    }

    public Statement getStatementAt(int index) {
        if (this.body != null && index == 0)
            return this.body;
        throw new ArrayIndexOutOfBoundsException();
    }

    public ASTList<LoopInitializer> getInitializers() {
        return this.inits;
    }

    public void setInitializers(ASTList<LoopInitializer> list) {
        this.inits = list;
    }

    public ASTList<Expression> getUpdates() {
        return this.updates;
    }

    public void setUpdates(ASTList<Expression> list) {
        this.updates = list;
    }

    public abstract boolean isExitCondition();

    public abstract boolean isCheckedBeforeIteration();
}
