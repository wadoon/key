package recoder.java.declaration;

import recoder.abstraction.AnnotationUse;
import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTList;

public class AnnotationUseSpecification extends JavaNonTerminalProgramElement implements AnnotationUse, DeclarationSpecifier, TypeReferenceContainer, Expression {
    private static final long serialVersionUID = 6354411799881814722L;

    protected NonTerminalProgramElement parent;

    protected TypeReference reference;

    protected ASTList<AnnotationElementValuePair> elementValuePairs;

    public AnnotationUseSpecification() {
    }

    public AnnotationUseSpecification(TypeReference reference) {
        this.reference = reference;
        makeParentRoleValid();
    }

    public AnnotationUseSpecification(AnnotationUseSpecification proto) {
        super(proto);
        this.reference = (TypeReference) proto.parent.deepClone();
        this.elementValuePairs = proto.elementValuePairs.deepClone();
        makeParentRoleValid();
    }

    public void accept(SourceVisitor v) {
        v.visitAnnotationUse(this);
    }

    public AnnotationUseSpecification deepClone() {
        return new AnnotationUseSpecification(this);
    }

    public int getChildCount() {
        int res = 0;
        if (this.reference != null)
            res++;
        if (this.elementValuePairs != null)
            res += this.elementValuePairs.size();
        return res;
    }

    public ProgramElement getChildAt(int index) {
        if (this.reference != null) {
            if (index == 0)
                return this.reference;
            index--;
        }
        return this.elementValuePairs.get(index);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (child == null)
            throw new NullPointerException();
        if (child == this.reference)
            return 0;
        if (this.elementValuePairs != null) {
            int idx = this.elementValuePairs.indexOf(child);
            if (idx >= -1)
                return idx << 4 | 0x1;
        }
        return -1;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.reference != null)
            this.reference.setParent(this);
        if (this.elementValuePairs != null)
            for (int i = 0, max = this.elementValuePairs.size(); i < max; i++)
                this.elementValuePairs.get(i).setParent(this);
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (p == this.reference) {
            TypeReference tr = (TypeReference) q;
            this.reference = tr;
            if (tr != null)
                tr.setParent(this);
            return true;
        }
        for (int i = 0; i < this.elementValuePairs.size(); i++) {
            AnnotationElementValuePair evp = this.elementValuePairs.get(i);
            if (p == evp)
                if (q == null) {
                    this.elementValuePairs.remove(i);
                } else {
                    AnnotationElementValuePair r = (AnnotationElementValuePair) q;
                    this.elementValuePairs.set(i, r);
                    r.setParent(this);
                }
        }
        return false;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public Declaration getParentDeclaration() {
        return (this.parent instanceof Declaration) ? (Declaration) this.parent : null;
    }

    public void setParent(Declaration parent) {
        this.parent = parent;
    }

    public void setParent(PackageSpecification parent) {
        this.parent = parent;
    }

    public TypeReference getTypeReference() {
        return this.reference;
    }

    public void setTypeReference(TypeReference tr) {
        this.reference = tr;
    }

    public int getTypeReferenceCount() {
        return (this.reference == null) ? 0 : 1;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (index == 0 && this.reference != null)
            return this.reference;
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public ASTList<AnnotationElementValuePair> getElementValuePairs() {
        return this.elementValuePairs;
    }

    public void setElementValuePairs(ASTList<AnnotationElementValuePair> elementValuePairs) {
        this.elementValuePairs = elementValuePairs;
    }

    public ExpressionContainer getExpressionContainer() {
        return (this.parent instanceof ExpressionContainer) ? (ExpressionContainer) this.parent : null;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.parent = c;
    }
}
