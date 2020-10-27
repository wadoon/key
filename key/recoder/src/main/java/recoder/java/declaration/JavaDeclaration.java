package recoder.java.declaration;

import recoder.java.Declaration;
import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.JavaProgramElement;
import recoder.java.declaration.modifier.*;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.List;

public abstract class JavaDeclaration extends JavaNonTerminalProgramElement implements Declaration {
    protected ASTList<DeclarationSpecifier> declarationSpecifiers;

    public JavaDeclaration() {
    }

    public JavaDeclaration(ASTList<DeclarationSpecifier> mods) {
        setDeclarationSpecifiers(mods);
    }

    protected JavaDeclaration(JavaDeclaration proto) {
        super(proto);
        if (proto.declarationSpecifiers != null)
            this.declarationSpecifiers = proto.declarationSpecifiers.deepClone();
    }

    public List<Modifier> getModifiers() {
        if (this.declarationSpecifiers == null)
            return new ArrayList<Modifier>(0);
        List<Modifier> mml = new ArrayList<Modifier>();
        for (int i = 0, max = this.declarationSpecifiers.size(); i < max; i++) {
            DeclarationSpecifier ds = this.declarationSpecifiers.get(i);
            if (ds instanceof Modifier)
                mml.add((Modifier) ds);
        }
        return mml;
    }

    public List<AnnotationUseSpecification> getAnnotations() {
        if (this.declarationSpecifiers == null)
            return new ArrayList<AnnotationUseSpecification>(0);
        List<AnnotationUseSpecification> result = new ArrayList<AnnotationUseSpecification>(this.declarationSpecifiers.size());
        int s = this.declarationSpecifiers.size();
        for (int i = 0; i < s; i++) {
            DeclarationSpecifier ds = this.declarationSpecifiers.get(i);
            if (ds instanceof AnnotationUseSpecification)
                result.add((AnnotationUseSpecification) ds);
        }
        return result;
    }

    public ASTList<DeclarationSpecifier> getDeclarationSpecifiers() {
        return this.declarationSpecifiers;
    }

    public void setDeclarationSpecifiers(ASTList<DeclarationSpecifier> m) {
        this.declarationSpecifiers = m;
    }

    public VisibilityModifier getVisibilityModifier() {
        if (this.declarationSpecifiers == null)
            return null;
        for (int i = this.declarationSpecifiers.size() - 1; i >= 0; i--) {
            DeclarationSpecifier m = this.declarationSpecifiers.get(i);
            if (m instanceof VisibilityModifier)
                return (VisibilityModifier) m;
        }
        return null;
    }

    final boolean containsModifier(Class type) {
        int s = (this.declarationSpecifiers == null) ? 0 : this.declarationSpecifiers.size();
        for (int i = 0; i < s; i++) {
            if (type.isInstance(this.declarationSpecifiers.get(i)))
                return true;
        }
        return false;
    }

    protected boolean isAbstract() {
        return containsModifier(Abstract.class);
    }

    protected boolean isPrivate() {
        return containsModifier(Private.class);
    }

    protected boolean isProtected() {
        return containsModifier(Protected.class);
    }

    protected boolean isPublic() {
        return containsModifier(Public.class);
    }

    protected boolean isStatic() {
        return containsModifier(Static.class);
    }

    protected boolean isTransient() {
        return containsModifier(Transient.class);
    }

    protected boolean isVolatile() {
        return containsModifier(Volatile.class);
    }

    protected boolean isStrictFp() {
        return containsModifier(StrictFp.class);
    }

    protected boolean isFinal() {
        return containsModifier(Final.class);
    }

    protected boolean isNative() {
        return containsModifier(Native.class);
    }

    protected boolean isSynchronized() {
        return containsModifier(Synchronized.class);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.declarationSpecifiers != null)
            for (int i = this.declarationSpecifiers.size() - 1; i >= 0; i--)
                this.declarationSpecifiers.get(i).setParent(this);
    }
}
