package recoder.java.statement;

import recoder.java.LoopInitializer;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.VariableScope;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.util.Debug;

import java.util.List;

public class EnhancedFor extends LoopStatement implements VariableScope {
    private static final long serialVersionUID = -4531341585909005502L;

    public EnhancedFor() {
    }

    public EnhancedFor(Statement body) {
        super(body);
        makeParentRoleValid();
    }

    protected EnhancedFor(EnhancedFor proto) {
        super(proto);
        makeParentRoleValid();
    }

    public boolean isExitCondition() {
        return false;
    }

    public boolean isCheckedBeforeIteration() {
        return true;
    }

    public List<VariableSpecification> getVariablesInScope() {
        LoopInitializer li = this.inits.get(0);
        return ((LocalVariableDeclaration) li).getVariables();
    }

    public VariableSpecification getVariableInScope(String name) {
        VariableSpecification var = getVariablesInScope().get(0);
        if (var.getName().equals(name))
            return var;
        return null;
    }

    public void addVariableToScope(VariableSpecification var) {
        Debug.assertNonnull(var);
        if (var != getVariablesInScope().get(0))
            throw new IllegalArgumentException();
    }

    public void removeVariableFromScope(String name) {
        throw new UnsupportedOperationException();
    }

    public boolean isDefinedScope() {
        return true;
    }

    public void setDefinedScope(boolean defined) {
    }

    public void accept(SourceVisitor v) {
        v.visitEnhancedFor(this);
    }

    public EnhancedFor deepClone() {
        return new EnhancedFor(this);
    }
}
