package recoder.java.declaration;

import recoder.java.Identifier;
import recoder.java.SourceVisitor;
import recoder.list.generic.ASTList;

public class AnnotationDeclaration extends InterfaceDeclaration {
    private static final long serialVersionUID = -5764583750285766921L;

    public AnnotationDeclaration() {
    }

    public AnnotationDeclaration(ASTList<DeclarationSpecifier> modifiers, Identifier name, ASTList<MemberDeclaration> members) {
        super(modifiers, name, null, members);
    }

    protected AnnotationDeclaration(AnnotationDeclaration proto) {
        super(proto);
    }

    public boolean isInterface() {
        return true;
    }

    public boolean isOrdinaryInterface() {
        return false;
    }

    public boolean isAnnotationType() {
        return true;
    }

    public boolean isEnumType() {
        return false;
    }

    public boolean isOrdinaryClass() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitAnnotationDeclaration(this);
    }

    public AnnotationDeclaration deepClone() {
        return new AnnotationDeclaration(this);
    }
}
