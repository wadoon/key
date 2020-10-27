package recoder.java.statement;

import recoder.java.*;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.List;

public class For extends LoopStatement implements VariableScope {
    private static final long serialVersionUID = 6315865704532091022L;

    public For() {
    }

    public For(ASTList<LoopInitializer> inits, Expression guard, ASTList<Expression> updates, Statement body) {
        super(body);
        setInitializers(inits);
        setGuard(guard);
        setUpdates(updates);
        makeParentRoleValid();
    }

    protected For(For proto) {
        super(proto);
        makeParentRoleValid();
    }

    public For deepClone() {
        return new For(this);
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

    public boolean isDefinedScope() {
        return true;
    }

    public void setDefinedScope(boolean defined) {
    }

    public List<VariableSpecification> getVariablesInScope() {
        if (this.inits != null) {
            LoopInitializer li = this.inits.get(0);
            if (li instanceof LocalVariableDeclaration)
                return ((LocalVariableDeclaration) li).getVariables();
        }
        return new ArrayList<VariableSpecification>();
    }

    public VariableSpecification getVariableInScope(String name) {
        Debug.assertNonnull(name);
        if (this.inits != null) {
            LoopInitializer li = this.inits.get(0);
            if (li instanceof LocalVariableDeclaration) {
                List<VariableSpecification> vars = ((LocalVariableDeclaration) li).getVariables();
                for (int i = 0, s = vars.size(); i < s; i++) {
                    VariableSpecification v = vars.get(i);
                    if (name.equals(v.getName()))
                        return v;
                }
            }
        }
        return null;
    }

    public void addVariableToScope(VariableSpecification var) {
        Debug.assertNonnull(var);
    }

    public void removeVariableFromScope(String name) {
        Debug.assertNonnull(name);
    }

    public void accept(SourceVisitor v) {
        v.visitFor(this);
    }
}
