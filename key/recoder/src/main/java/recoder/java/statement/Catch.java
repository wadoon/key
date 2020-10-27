package recoder.java.statement;

import recoder.java.*;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.List;

public class Catch extends Branch implements ParameterContainer, VariableScope {
    private static final long serialVersionUID = -6747731923114431193L;

    protected ParameterDeclaration parameter;

    protected StatementBlock body;

    public Catch() {
    }

    public Catch(ParameterDeclaration e, StatementBlock body) {
        setBody(body);
        setParameterDeclaration(e);
        makeParentRoleValid();
    }

    protected Catch(Catch proto) {
        super(proto);
        if (proto.parameter != null)
            this.parameter = proto.parameter.deepClone();
        if (proto.body != null)
            this.body = proto.body.deepClone();
        makeParentRoleValid();
    }

    public Catch deepClone() {
        return new Catch(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.parameter != null)
            this.parameter.setParameterContainer(this);
        if (this.body != null)
            this.body.setStatementContainer(this);
    }

    public SourceElement getLastElement() {
        return (this.body != null) ? this.body.getLastElement() : this;
    }

    public int getChildCount() {
        int result = 0;
        if (this.parameter != null)
            result++;
        if (this.body != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.parameter != null) {
            if (index == 0)
                return this.parameter;
            index--;
        }
        if (this.body != null) {
            if (index == 0)
                return this.body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.parameter == child)
            return 0;
        if (this.body == child)
            return 1;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.parameter == p) {
            ParameterDeclaration r = (ParameterDeclaration) q;
            this.parameter = r;
            if (r != null)
                r.setParameterContainer(this);
            return true;
        }
        if (this.body == p) {
            StatementBlock r = (StatementBlock) q;
            this.body = r;
            if (r != null)
                r.setStatementContainer(this);
            return true;
        }
        return false;
    }

    public int getStatementCount() {
        return (this.body != null) ? 1 : 0;
    }

    public Statement getStatementAt(int index) {
        if (this.body != null && index == 0)
            return this.body;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getParameterDeclarationCount() {
        return (this.parameter != null) ? 1 : 0;
    }

    public ParameterDeclaration getParameterDeclarationAt(int index) {
        if (this.parameter != null && index == 0)
            return this.parameter;
        throw new ArrayIndexOutOfBoundsException();
    }

    public Statement getBody() {
        return this.body;
    }

    public void setBody(Statement statement) {
        this.body = (StatementBlock) statement;
    }

    public void setParent(Try parent) {
        this.parent = parent;
    }

    public ParameterDeclaration getParameterDeclaration() {
        return this.parameter;
    }

    public void setParameterDeclaration(ParameterDeclaration p) {
        this.parameter = p;
    }

    public boolean isDefinedScope() {
        return true;
    }

    public void setDefinedScope(boolean defined) {
    }

    public List<VariableSpecification> getVariablesInScope() {
        if (this.parameter != null)
            return this.parameter.getVariables();
        return new ArrayList<VariableSpecification>(0);
    }

    public VariableSpecification getVariableInScope(String name) {
        Debug.assertNonnull(name);
        if (this.parameter != null) {
            VariableSpecification v = this.parameter.getVariableSpecification();
            if (name.equals(v.getName()))
                return v;
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
        v.visitCatch(this);
    }
}
