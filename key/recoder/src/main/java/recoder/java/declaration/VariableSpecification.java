package recoder.java.declaration;

import recoder.abstraction.ProgramModelElement;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.java.*;
import recoder.list.generic.ASTList;
import recoder.service.ProgramModelInfo;

public class VariableSpecification extends JavaNonTerminalProgramElement implements Declaration, NamedProgramElement, ExpressionContainer, Variable {
    private static final long serialVersionUID = -2190909599303924076L;

    protected VariableDeclaration parent;

    protected Identifier name;

    protected Expression initializer;

    protected int dimensions;

    protected ProgramModelInfo service;

    public VariableSpecification() {
    }

    public VariableSpecification(Identifier name) {
        setIdentifier(name);
        makeParentRoleValid();
    }

    public VariableSpecification(Identifier name, Expression init) {
        setParent(this.parent);
        setIdentifier(name);
        setInitializer(init);
        makeParentRoleValid();
    }

    public VariableSpecification(Identifier name, int dimensions, Expression init) {
        setParent(this.parent);
        setIdentifier(name);
        setDimensions(dimensions);
        setInitializer(init);
        makeParentRoleValid();
    }

    protected VariableSpecification(VariableSpecification proto) {
        super(proto);
        if (proto.name != null)
            this.name = proto.name.deepClone();
        if (proto.initializer != null)
            this.initializer = proto.initializer.deepClone();
        this.dimensions = proto.dimensions;
        makeParentRoleValid();
    }

    private static void updateModel() {
        factory.getServiceConfiguration().getChangeHistory().updateModel();
    }

    public VariableSpecification deepClone() {
        return new VariableSpecification(this);
    }

    public void makeParentRoleValid() {
        if (this.name != null)
            this.name.setParent(this);
        if (this.initializer != null)
            this.initializer.setExpressionContainer(this);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public int getChildCount() {
        int result = 0;
        if (this.name != null)
            result++;
        if (this.initializer != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.name != null) {
            if (index == 0)
                return this.name;
            index--;
        }
        if (this.initializer != null &&
                index == 0)
            return this.initializer;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.name == child)
            return 0;
        if (this.initializer == child)
            return 1;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.name == p) {
            Identifier r = (Identifier) q;
            this.name = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        if (this.initializer == p) {
            Expression r = (Expression) q;
            this.initializer = r;
            if (r != null)
                r.setExpressionContainer(this);
            return true;
        }
        return false;
    }

    public VariableDeclaration getParent() {
        return this.parent;
    }

    public void setParent(VariableDeclaration parent) {
        this.parent = parent;
    }

    public int getExpressionCount() {
        return (this.initializer != null) ? 1 : 0;
    }

    public Expression getExpressionAt(int index) {
        if (this.initializer != null && index == 0)
            return this.initializer;
        throw new ArrayIndexOutOfBoundsException();
    }

    public final String getName() {
        return (this.name == null) ? null : this.name.getText();
    }

    public Identifier getIdentifier() {
        return this.name;
    }

    public void setIdentifier(Identifier id) {
        this.name = id;
    }

    public int getDimensions() {
        return this.dimensions;
    }

    public void setDimensions(int dimensions) {
        if (dimensions < 0)
            throw new IllegalArgumentException("Negative dimension?");
        this.dimensions = dimensions;
    }

    public Expression getInitializer() {
        return this.initializer;
    }

    public void setInitializer(Expression expr) {
        this.initializer = expr;
    }

    public ASTList<DeclarationSpecifier> getDeclarationSpecifiers() {
        return (this.parent != null) ? this.parent.getDeclarationSpecifiers() : null;
    }

    public void setDeclarationSpecifiers(ASTList<DeclarationSpecifier> m) {
        if (this.parent != null)
            this.parent.setDeclarationSpecifiers(m);
    }

    public boolean isStrictFp() {
        return this.parent.isStrictFp();
    }

    public boolean isFinal() {
        return this.parent.isFinal();
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.service;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.service = service;
    }

    public Type getType() {
        if (this.service == null)
            updateModel();
        return this.service.getType(this);
    }

    public String getFullName() {
        return getName();
    }

    public SourceElement getFirstElement() {
        return this.name;
    }

    public SourceElement getLastElement() {
        if (this.initializer != null)
            return this.initializer.getLastElement();
        return this.name;
    }

    public void accept(SourceVisitor v) {
        v.visitVariableSpecification(this);
    }
}
