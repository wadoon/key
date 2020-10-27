package recoder.java.statement;

import recoder.abstraction.ClassType;
import recoder.java.*;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Switch extends BranchStatement implements ExpressionContainer, VariableScope, TypeScope {
    protected static final Map UNDEFINED_SCOPE = new HashMap<Object, Object>(1);
    private static final long serialVersionUID = 1L;
    protected ASTList<Branch> branches;
    protected Expression expression;
    protected Map<String, TypeDeclaration> name2type = UNDEFINED_SCOPE;

    protected Map<String, VariableSpecification> name2var = UNDEFINED_SCOPE;

    public Switch(Expression e) {
        setExpression(e);
        makeParentRoleValid();
    }

    public Switch(Expression e, ASTList<Branch> branches) {
        setBranchList(branches);
        setExpression(e);
        makeParentRoleValid();
    }

    protected Switch(Switch proto) {
        super(proto);
        if (proto.expression != null)
            this.expression = proto.expression.deepClone();
        if (proto.branches != null)
            this.branches = proto.branches.deepClone();
        makeParentRoleValid();
    }

    public Switch() {
    }

    public Switch deepClone() {
        return new Switch(this);
    }

    public int getChildCount() {
        int result = 0;
        if (this.expression != null)
            result++;
        if (this.branches != null)
            result += this.branches.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.expression != null) {
            if (index == 0)
                return this.expression;
            index--;
        }
        if (this.branches != null)
            return this.branches.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.expression == child)
            return 0;
        if (this.branches != null) {
            int index = this.branches.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x1;
        }
        return -1;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.expression != null)
            this.expression.setExpressionContainer(this);
        if (this.branches != null)
            for (int i = this.branches.size() - 1; i >= 0; i--) {
                Branch b = this.branches.get(i);
                if (b instanceof Case) {
                    ((Case) b).setParent(this);
                } else {
                    ((Default) b).setParent(this);
                }
            }
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.expression == p) {
            Expression r = (Expression) q;
            this.expression = r;
            if (r != null)
                r.setExpressionContainer(this);
            return true;
        }
        int count = (this.branches == null) ? 0 : this.branches.size();
        for (int i = 0; i < count; i++) {
            if (this.branches.get(i) == p) {
                if (q == null) {
                    this.branches.remove(i);
                } else if (q instanceof Case) {
                    this.branches.set(i, q);
                    ((Case) q).setParent(this);
                } else {
                    this.branches.set(i, q);
                    ((Default) q).setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public int getExpressionCount() {
        return (this.expression != null) ? 1 : 0;
    }

    public Expression getExpressionAt(int index) {
        if (this.expression != null && index == 0)
            return this.expression;
        throw new ArrayIndexOutOfBoundsException();
    }

    public Expression getExpression() {
        return this.expression;
    }

    public void setExpression(Expression e) {
        if (e == null)
            throw new NullPointerException("Switches must have an expression");
        this.expression = e;
    }

    public ASTList<Branch> getBranchList() {
        return this.branches;
    }

    public void setBranchList(ASTList<Branch> branches) {
        this.branches = branches;
    }

    public int getBranchCount() {
        return (this.branches != null) ? this.branches.size() : 0;
    }

    public Branch getBranchAt(int index) {
        if (this.branches != null)
            return this.branches.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean isDefinedScope() {
        return (this.name2type != UNDEFINED_SCOPE);
    }

    public void setDefinedScope(boolean defined) {
        if (!defined) {
            this.name2type = UNDEFINED_SCOPE;
            this.name2var = UNDEFINED_SCOPE;
        } else if (this.name2type == UNDEFINED_SCOPE) {
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
            return new ArrayList<VariableSpecification>(0);
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
        v.visitSwitch(this);
    }

    public SourceElement getLastElement() {
        if (getBranchCount() == 0)
            return this;
        return getBranchAt(getBranchCount() - 1).getLastElement();
    }
}
