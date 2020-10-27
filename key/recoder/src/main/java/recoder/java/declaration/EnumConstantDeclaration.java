package recoder.java.declaration;

import recoder.ModelException;
import recoder.java.NonTerminalProgramElement;
import recoder.java.SourceVisitor;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class EnumConstantDeclaration extends FieldDeclaration implements MemberDeclaration {
    private static final long serialVersionUID = 6254325025698455465L;

    public EnumConstantDeclaration() {
    }

    public EnumConstantDeclaration(EnumConstantSpecification spec, ASTList<DeclarationSpecifier> annotations) {
        setEnumConstantSpecification(spec);
        setDeclarationSpecifiers(annotations);
        makeParentRoleValid();
    }

    protected EnumConstantDeclaration(EnumConstantDeclaration proto) {
        super(proto);
        makeParentRoleValid();
    }

    public EnumDeclaration getParent() {
        return (EnumDeclaration) this.parent;
    }

    public void accept(SourceVisitor v) {
        v.visitEnumConstantDeclaration(this);
    }

    public boolean isFinal() {
        return true;
    }

    public boolean isStatic() {
        return true;
    }

    public boolean isPrivate() {
        return false;
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPublic() {
        return true;
    }

    public boolean isStrictFp() {
        return false;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public EnumConstantDeclaration deepClone() {
        return new EnumConstantDeclaration(this);
    }

    public EnumConstantSpecification getEnumConstantSpecification() {
        if (this.fieldSpecs == null || this.fieldSpecs.size() == 0)
            return null;
        return (EnumConstantSpecification) this.fieldSpecs.get(0);
    }

    public void setEnumConstantSpecification(EnumConstantSpecification spec) {
        if (this.fieldSpecs == null)
            this.fieldSpecs = (ASTList<FieldSpecification>) new ASTArrayList(1);
        this.fieldSpecs.add(spec);
    }

    public TypeDeclaration getMemberParent() {
        return this.parent;
    }

    public void setMemberParent(TypeDeclaration t) {
        if (!(t instanceof EnumDeclaration))
            throw new IllegalArgumentException("Only an EnumDeclarations can be parent of an EnumConstantDeclaration");
        super.setMemberParent(t);
    }

    public void validate() throws ModelException {
        if (this.typeReference != null)
            throw new ModelException("TypeReference set in EnumConstantDeclaration in " + this.parent.getFullName());
        if (this.declarationSpecifiers != null)
            for (int i = 0; i < this.declarationSpecifiers.size(); i++) {
                DeclarationSpecifier ds = this.declarationSpecifiers.get(i);
                if (!(ds instanceof recoder.abstraction.AnnotationUse))
                    throw new ModelException("EnumConstantDeclaration may not contain modifiers in " + this.parent.getFullName());
            }
        if (!(this.parent instanceof EnumDeclaration))
            throw new ModelException("Illegal parent type (" + this.parent.getClass().getCanonicalName() + " - " + this.parent.getFullName() + ") for EnumConstantDeclaration");
        if (this.fieldSpecs.size() != 1)
            throw new ModelException("Only one EnumConstantSpecification per EnumConstantDeclaration allowed in " + this.parent.getFullName());
        if (!(this.fieldSpecs.get(0) instanceof EnumConstantSpecification))
            throw new ModelException("child of EnumConstantDeclaration is not an EnumConstantSpecification in " + this.parent.getFullName());
    }
}
