package recoder.java.reference;

import recoder.java.*;

public class PackageReference extends JavaNonTerminalProgramElement implements TypeReferenceInfix, PackageReferenceContainer {
    private static final long serialVersionUID = -4209613321578432317L;

    protected ReferencePrefix prefix;

    protected PackageReferenceContainer parent;

    protected Identifier name;

    public PackageReference() {
    }

    public PackageReference(Identifier id) {
        setIdentifier(id);
        makeParentRoleValid();
    }

    public PackageReference(PackageReference path, Identifier id) {
        setReferencePrefix(path);
        setIdentifier(id);
        makeParentRoleValid();
    }

    protected PackageReference(PackageReference proto) {
        super(proto);
        if (proto.prefix != null)
            this.prefix = (ReferencePrefix) proto.prefix.deepClone();
        if (proto.name != null)
            this.name = proto.name.deepClone();
        makeParentRoleValid();
    }

    public PackageReference deepClone() {
        return new PackageReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.prefix != null)
            this.prefix.setReferenceSuffix(this);
        if (this.name != null)
            this.name.setParent(this);
    }

    public SourceElement getFirstElement() {
        return (this.prefix == null) ? this.name : this.prefix.getFirstElement();
    }

    public SourceElement getLastElement() {
        return this.name;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public int getChildCount() {
        int result = 0;
        if (this.prefix != null)
            result++;
        if (this.name != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.prefix != null) {
            if (index == 0)
                return this.prefix;
            index--;
        }
        if (this.name != null &&
                index == 0)
            return this.name;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.prefix == child)
            return 0;
        if (this.name == child)
            return 1;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.prefix == p) {
            PackageReference r = (PackageReference) q;
            this.prefix = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        if (this.name == p) {
            Identifier r = (Identifier) q;
            this.name = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        return false;
    }

    public void setParent(PackageReferenceContainer parent) {
        this.parent = parent;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.prefix;
    }

    public void setReferencePrefix(ReferencePrefix prefix) {
        this.prefix = prefix;
    }

    public PackageReference getPackageReference() {
        return (this.prefix instanceof PackageReference) ? (PackageReference) this.prefix : null;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return (this.parent instanceof ReferenceSuffix) ? (ReferenceSuffix) this.parent : null;
    }

    public void setReferenceSuffix(ReferenceSuffix x) {
        this.parent = (PackageReferenceContainer) x;
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

    public void accept(SourceVisitor v) {
        v.visitPackageReference(this);
    }
}
