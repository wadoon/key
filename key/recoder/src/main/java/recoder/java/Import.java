package recoder.java;

import recoder.java.reference.*;

public class Import extends JavaNonTerminalProgramElement implements TypeReferenceContainer, PackageReferenceContainer {
    private static final long serialVersionUID = -722260309045817264L;

    protected boolean isMultiImport;

    protected boolean isStaticImport;

    protected CompilationUnit parent;

    protected TypeReferenceInfix reference;

    protected Identifier staticIdentifier;

    public Import() {
    }

    public Import(TypeReference t, boolean multi) {
        setReference(t);
        setMultiImport(multi);
        makeParentRoleValid();
    }

    public Import(TypeReference t, Identifier id) {
        setReference(t);
        setStaticIdentifier(id);
        setMultiImport(false);
        setStaticImport(true);
        makeParentRoleValid();
    }

    public Import(TypeReference t, boolean multi, boolean isStatic) {
        setReference(t);
        setMultiImport(multi);
        setStaticImport(isStatic);
        makeParentRoleValid();
    }

    public Import(PackageReference t) {
        setReference(t);
        setMultiImport(true);
        setStaticImport(false);
        makeParentRoleValid();
    }

    protected Import(Import proto) {
        super(proto);
        if (proto.reference != null)
            this.reference = (TypeReferenceInfix) proto.reference.deepClone();
        if (proto.staticIdentifier != null)
            this.staticIdentifier = proto.staticIdentifier.deepClone();
        this.isMultiImport = proto.isMultiImport;
        this.isStaticImport = proto.isStaticImport;
        makeParentRoleValid();
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.staticIdentifier != null)
            this.staticIdentifier.setParent(this);
        if (this.reference instanceof TypeReference) {
            ((TypeReference) this.reference).setParent(this);
        } else if (this.reference instanceof PackageReference) {
            ((PackageReference) this.reference).setParent(this);
        } else if (this.reference instanceof UncollatedReferenceQualifier) {
            ((UncollatedReferenceQualifier) this.reference).setParent(this);
        } else {
            throw new IllegalStateException("Unknown reference type encountered");
        }
    }

    public Import deepClone() {
        return new Import(this);
    }

    public SourceElement getLastElement() {
        return this.reference.getLastElement();
    }

    public boolean isMultiImport() {
        return this.isMultiImport;
    }

    public void setMultiImport(boolean multi) {
        if (!multi && this.reference instanceof PackageReference)
            throw new IllegalArgumentException("Package imports are always multi");
        this.isMultiImport = multi;
    }

    public boolean isStaticImport() {
        return this.isStaticImport;
    }

    public void setStaticImport(boolean isStatic) {
        this.isStaticImport = isStatic;
    }

    public Identifier getStaticIdentifier() {
        return this.staticIdentifier;
    }

    public void setStaticIdentifier(Identifier id) {
        this.staticIdentifier = id;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public int getChildCount() {
        int result = 0;
        if (this.reference != null)
            result++;
        if (this.staticIdentifier != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.reference != null) {
            if (index == 0)
                return this.reference;
            index--;
        }
        if (index == 0 && this.staticIdentifier != null)
            return this.staticIdentifier;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (child == this.reference)
            return 0;
        if (child == this.staticIdentifier)
            return 1;
        return -1;
    }

    public CompilationUnit getParent() {
        return this.parent;
    }

    public void setParent(CompilationUnit u) {
        this.parent = u;
    }

    public int getTypeReferenceCount() {
        return (this.reference instanceof TypeReference) ? 1 : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.reference instanceof TypeReference && index == 0)
            return (TypeReference) this.reference;
        throw new ArrayIndexOutOfBoundsException();
    }

    public TypeReference getTypeReference() {
        return (this.reference instanceof TypeReference) ? (TypeReference) this.reference : null;
    }

    public PackageReference getPackageReference() {
        return (this.reference instanceof PackageReference) ? (PackageReference) this.reference : null;
    }

    public TypeReferenceInfix getReference() {
        return this.reference;
    }

    public void setReference(TypeReferenceInfix t) {
        this.reference = t;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.reference == p) {
            TypeReferenceInfix r = (TypeReferenceInfix) q;
            this.reference = r;
            if (r instanceof TypeReference) {
                ((TypeReference) r).setParent(this);
            } else if (r instanceof PackageReference) {
                ((PackageReference) r).setParent(this);
                this.isMultiImport = true;
            }
            return true;
        }
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitImport(this);
    }
}
