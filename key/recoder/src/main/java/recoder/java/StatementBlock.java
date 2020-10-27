package recoder.java;

import recoder.abstraction.ClassType;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.TypeDeclarationContainer;
import recoder.java.declaration.VariableSpecification;
import recoder.java.statement.JavaStatement;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class StatementBlock extends JavaStatement implements StatementContainer, TypeDeclarationContainer, VariableScope, TypeScope {
    protected static final Map UNDEFINED_SCOPE = new HashMap<Object, Object>(1);
    private static final long serialVersionUID = -3288497346043639754L;
    protected ASTList<Statement> body;
    protected Map<String, TypeDeclaration> name2type = UNDEFINED_SCOPE;

    protected Map<String, VariableSpecification> name2var = UNDEFINED_SCOPE;

    public StatementBlock(ASTList<Statement> block) {
        setBody(block);
        makeParentRoleValid();
    }

    protected StatementBlock(StatementBlock proto) {
        super(proto);
        if (proto.body != null)
            this.body = proto.body.deepClone();
        makeParentRoleValid();
    }

    public StatementBlock() {
    }

    public StatementBlock deepClone() {
        return new StatementBlock(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.body != null)
            for (int i = this.body.size() - 1; i >= 0; i--)
                this.body.get(i).setStatementContainer(this);
    }

    public ASTList<Statement> getBody() {
        return this.body;
    }

    public void setBody(ASTList<Statement> list) {
        this.body = list;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.body == null) ? 0 : this.body.size();
        for (int i = 0; i < count; i++) {
            if (this.body.get(i) == p) {
                if (q == null) {
                    this.body.remove(i);
                } else {
                    Statement r = (Statement) q;
                    this.body.set(i, r);
                    r.setStatementContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    public int getChildCount() {
        return (this.body != null) ? this.body.size() : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.body != null) {
            int len = this.body.size();
            if (len > index)
                return this.body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.body != null) {
            int index = this.body.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        return -1;
    }

    public int getStatementCount() {
        return (this.body != null) ? this.body.size() : 0;
    }

    public Statement getStatementAt(int index) {
        if (this.body != null)
            return this.body.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getTypeDeclarationCount() {
        int count = 0;
        if (this.body != null)
            for (int i = this.body.size() - 1; i >= 0; i--) {
                if (this.body.get(i) instanceof TypeDeclaration)
                    count++;
            }
        return count;
    }

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (this.body != null) {
            int s = this.body.size();
            for (int i = 0; i < s && index >= 0; i++) {
                Statement st = this.body.get(i);
                if (st instanceof TypeDeclaration) {
                    if (index == 0)
                        return (TypeDeclaration) st;
                    index--;
                }
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean isDefinedScope() {
        return (this.name2type != UNDEFINED_SCOPE);
    }

    public void setDefinedScope(boolean defined) {
        if (!defined) {
            this.name2type = UNDEFINED_SCOPE;
            this.name2var = UNDEFINED_SCOPE;
        } else {
            this.name2type = null;
            this.name2var = null;
        }
    }

    public List<TypeDeclaration> getTypesInScope() {
        if (this.name2type == null || this.name2type.isEmpty())
            return new ArrayList<TypeDeclaration>(0);
        List<TypeDeclaration> res = new ArrayList<TypeDeclaration>();
        for (TypeDeclaration td : this.name2type.values())
            res.add(td);
        return res;
    }

    public ClassType getTypeInScope(String name) {
        Debug.assertNonnull(name);
        if (this.name2type == null)
            return null;
        return this.name2type.get(name);
    }

    public void addTypeToScope(ClassType type, String name) {
        Debug.assertNonnull(type, name);
        if (this.name2type == null || this.name2type == UNDEFINED_SCOPE)
            this.name2type = new HashMap<String, TypeDeclaration>();
        this.name2type.put(name, (TypeDeclaration) type);
    }

    public void removeTypeFromScope(String name) {
        Debug.assertNonnull(name);
        if (this.name2type == null || this.name2type == UNDEFINED_SCOPE)
            return;
        this.name2type.remove(name);
    }

    public List<VariableSpecification> getVariablesInScope() {
        if (this.name2var == null || this.name2var.isEmpty())
            return new ArrayList<VariableSpecification>();
        List<VariableSpecification> res = new ArrayList<VariableSpecification>();
        for (VariableSpecification vs : this.name2var.values())
            res.add(vs);
        return res;
    }

    public VariableSpecification getVariableInScope(String name) {
        Debug.assertNonnull(name);
        if (this.name2var == null)
            return null;
        return this.name2var.get(name);
    }

    public void addVariableToScope(VariableSpecification var) {
        Debug.assertNonnull(var);
        if (this.name2var == null || this.name2var == UNDEFINED_SCOPE)
            this.name2var = new HashMap<String, VariableSpecification>();
        this.name2var.put(var.getName(), var);
    }

    public void removeVariableFromScope(String name) {
        Debug.assertNonnull(name);
        if (this.name2var == null || this.name2var == UNDEFINED_SCOPE)
            return;
        this.name2var.remove(name);
    }

    public void accept(SourceVisitor v) {
        v.visitStatementBlock(this);
    }
}
