package recoder.java.declaration;

import recoder.abstraction.Constructor;
import recoder.java.Identifier;
import recoder.java.SourceVisitor;
import recoder.java.StatementBlock;
import recoder.java.declaration.modifier.VisibilityModifier;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class ConstructorDeclaration extends MethodDeclaration implements Constructor {
    private static final long serialVersionUID = -1852257105076401562L;

    public ConstructorDeclaration() {
    }

    public ConstructorDeclaration(VisibilityModifier modifier, Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions, StatementBlock body) {
        super(null, null, name, parameters, exceptions, body);
        ASTArrayList aSTArrayList = new ASTArrayList(1);
        if (aSTArrayList != null) {
            aSTArrayList.add(modifier);
            setDeclarationSpecifiers((ASTList<DeclarationSpecifier>) aSTArrayList);
        }
        makeParentRoleValid();
    }

    protected ConstructorDeclaration(ConstructorDeclaration proto) {
        super(proto);
    }

    public ConstructorDeclaration deepClone() {
        return new ConstructorDeclaration(this);
    }

    public boolean isAbstract() {
        return false;
    }

    public boolean isFinal() {
        return false;
    }

    public boolean isNative() {
        return false;
    }

    public boolean isStatic() {
        return false;
    }

    public boolean isStrictFp() {
        return false;
    }

    public boolean isSynchronized() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitConstructorDeclaration(this);
    }
}
