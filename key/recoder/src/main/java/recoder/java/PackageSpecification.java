package recoder.java;

import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.reference.PackageReference;
import recoder.java.reference.PackageReferenceContainer;
import recoder.list.generic.ASTList;

public class PackageSpecification extends JavaNonTerminalProgramElement implements PackageReferenceContainer {
    private static final long serialVersionUID = -6415275246661492494L;

    protected CompilationUnit parent;

    protected PackageReference reference;

    protected ASTList<AnnotationUseSpecification> annotations;

    public PackageSpecification() {
    }

    public PackageSpecification(PackageReference pkg) {
        setPackageReference(pkg);
        makeParentRoleValid();
    }

    protected PackageSpecification(PackageSpecification proto) {
        super(proto);
        if (proto.reference != null)
            this.reference = proto.reference.deepClone();
        makeParentRoleValid();
    }

    public PackageSpecification deepClone() {
        return new PackageSpecification(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        this.reference.setParent(this);
        if (this.annotations != null)
            for (int i = 0; i < this.annotations.size(); i++)
                this.annotations.get(i).setParent(this);
    }

    public SourceElement getLastElement() {
        return this.reference;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public int getChildCount() {
        int result = 0;
        if (this.reference != null)
            result++;
        if (this.annotations != null)
            result += this.annotations.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.reference != null) {
            if (index == 0)
                return this.reference;
            index--;
        }
        return this.annotations.get(index);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (child == this.reference)
            return 0;
        if (this.annotations != null) {
            int idx = this.annotations.indexOf(child);
            if (idx != -1)
                return idx << 4 | 0x1;
        }
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.reference == p) {
            PackageReference r = (PackageReference) q;
            this.reference = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        int idx = this.annotations.indexOf(p);
        if (idx != -1) {
            AnnotationUseSpecification aus = (AnnotationUseSpecification) q;
            this.annotations.set(idx, aus);
            if (aus != null)
                aus.setParent(this);
            return true;
        }
        return false;
    }

    public CompilationUnit getParent() {
        return this.parent;
    }

    public void setParent(CompilationUnit u) {
        this.parent = u;
    }

    public PackageReference getPackageReference() {
        return this.reference;
    }

    public void setPackageReference(PackageReference ref) {
        this.reference = ref;
    }

    public void accept(SourceVisitor v) {
        v.visitPackageSpecification(this);
    }

    public ASTList<AnnotationUseSpecification> getAnnotations() {
        return this.annotations;
    }

    public void setAnnotations(ASTList<AnnotationUseSpecification> annotations) {
        this.annotations = annotations;
    }
}
