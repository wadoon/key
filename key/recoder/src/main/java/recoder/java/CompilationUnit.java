package recoder.java;

import recoder.abstraction.ClassType;
import recoder.io.DataLocation;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.TypeDeclarationContainer;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class CompilationUnit extends JavaNonTerminalProgramElement implements TypeDeclarationContainer, TypeScope {
    protected static final Map UNDEFINED_SCOPE = new HashMap<Object, Object>(1);
    private static final long serialVersionUID = -1511486506045179278L;
    protected DataLocation location;
    protected DataLocation originalLocation;
    protected PackageSpecification packageSpec;
    protected ASTList<Import> imports;
    protected ASTList<TypeDeclaration> typeDeclarations;
    protected Map<String, ClassType> name2type = UNDEFINED_SCOPE;

    public CompilationUnit() {
        makeParentRoleValid();
    }

    public CompilationUnit(PackageSpecification pkg, ASTList<Import> imports, ASTList<TypeDeclaration> typeDeclarations) {
        setPackageSpecification(pkg);
        setImports(imports);
        setDeclarations(typeDeclarations);
        makeParentRoleValid();
    }

    protected CompilationUnit(CompilationUnit proto) {
        super(proto);
        if (proto.packageSpec != null)
            this.packageSpec = proto.packageSpec.deepClone();
        if (proto.imports != null)
            this.imports = proto.imports.deepClone();
        if (proto.typeDeclarations != null)
            this.typeDeclarations = proto.typeDeclarations.deepClone();
        makeParentRoleValid();
    }

    public CompilationUnit deepClone() {
        return new CompilationUnit(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.packageSpec != null)
            this.packageSpec.setParent(this);
        if (this.imports != null)
            for (int i = this.imports.size() - 1; i >= 0; i--)
                this.imports.get(i).setParent(this);
        if (this.typeDeclarations != null)
            for (int i = this.typeDeclarations.size() - 1; i >= 0; i--)
                this.typeDeclarations.get(i).setParent(this);
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.packageSpec == p) {
            PackageSpecification r = (PackageSpecification) q;
            this.packageSpec = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        int count = (this.imports == null) ? 0 : this.imports.size();
        int i;
        for (i = 0; i < count; i++) {
            if (this.imports.get(i) == p) {
                if (q == null) {
                    this.imports.remove(i);
                } else {
                    Import r = (Import) q;
                    this.imports.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        count = (this.typeDeclarations == null) ? 0 : this.typeDeclarations.size();
        for (i = 0; i < count; i++) {
            if (this.typeDeclarations.get(i) == p) {
                if (q == null) {
                    this.typeDeclarations.remove(i);
                } else {
                    TypeDeclaration r = (TypeDeclaration) q;
                    this.typeDeclarations.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public SourceElement getFirstElement() {
        return (getChildCount() > 0) ? getChildAt(0).getFirstElement() : this;
    }

    public SourceElement getLastElement() {
        return (this.typeDeclarations != null && !this.typeDeclarations.isEmpty()) ? this.typeDeclarations.get(this.typeDeclarations.size() - 1).getLastElement() : this;
    }

    public String getName() {
        return (this.location == null) ? "" : this.location.toString();
    }

    public NonTerminalProgramElement getASTParent() {
        return null;
    }

    public int getChildCount() {
        int result = 0;
        if (this.packageSpec != null)
            result++;
        if (this.imports != null)
            result += this.imports.size();
        if (this.typeDeclarations != null)
            result += this.typeDeclarations.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.packageSpec != null) {
            if (index == 0)
                return this.packageSpec;
            index--;
        }
        if (this.imports != null) {
            int len = this.imports.size();
            if (len > index)
                return this.imports.get(index);
            index -= len;
        }
        if (this.typeDeclarations != null)
            return this.typeDeclarations.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (child == this.packageSpec)
            return 0;
        if (this.imports != null) {
            int index = this.imports.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x1;
        }
        if (this.typeDeclarations != null) {
            int index = this.typeDeclarations.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x2;
        }
        return -1;
    }

    public DataLocation getDataLocation() {
        return this.location;
    }

    public void setDataLocation(DataLocation location) {
        if (this.location == null)
            this.originalLocation = location;
        this.location = location;
    }

    public DataLocation getOriginalDataLocation() {
        return this.originalLocation;
    }

    public ASTList<Import> getImports() {
        return this.imports;
    }

    public void setImports(ASTList<Import> list) {
        this.imports = list;
    }

    public PackageSpecification getPackageSpecification() {
        return this.packageSpec;
    }

    public void setPackageSpecification(PackageSpecification p) {
        this.packageSpec = p;
    }

    public int getTypeDeclarationCount() {
        return (this.typeDeclarations != null) ? this.typeDeclarations.size() : 0;
    }

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (this.typeDeclarations != null)
            return this.typeDeclarations.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public ASTList<TypeDeclaration> getDeclarations() {
        return this.typeDeclarations;
    }

    public void setDeclarations(ASTList<TypeDeclaration> list) {
        this.typeDeclarations = list;
    }

    public TypeDeclaration getPrimaryTypeDeclaration() {
        TypeDeclaration res = null;
        int s = this.typeDeclarations.size();
        for (int i = 0; i < s; i++) {
            TypeDeclaration t = this.typeDeclarations.get(i);
            if (t.isPublic()) {
                if (res == null || !res.isPublic()) {
                    res = t;
                } else {
                    res = null;
                    break;
                }
            } else if (res == null) {
                res = t;
            }
        }
        return res;
    }

    public boolean isDefinedScope() {
        return (this.name2type != UNDEFINED_SCOPE);
    }

    public void setDefinedScope(boolean defined) {
        if (!defined) {
            this.name2type = UNDEFINED_SCOPE;
        } else {
            this.name2type = null;
        }
    }

    public List<ClassType> getTypesInScope() {
        if (this.name2type == null || this.name2type.isEmpty())
            return new ArrayList<ClassType>(0);
        List<ClassType> res = new ArrayList<ClassType>();
        for (ClassType ct : this.name2type.values())
            res.add(ct);
        return res;
    }

    public ClassType getTypeInScope(String name) {
        Debug.assertNonnull(name);
        if (this.name2type == null || this.name2type == UNDEFINED_SCOPE)
            return null;
        return this.name2type.get(name);
    }

    public void addTypeToScope(ClassType type, String name) {
        Debug.assertNonnull(type, name);
        if (this.name2type == null || this.name2type == UNDEFINED_SCOPE)
            this.name2type = new HashMap<String, ClassType>();
        this.name2type.put(name, type);
    }

    public void removeTypeFromScope(String name) {
        Debug.assertNonnull(name);
        if (this.name2type == null || this.name2type == UNDEFINED_SCOPE)
            return;
        this.name2type.remove(name);
    }

    public void accept(SourceVisitor v) {
        v.visitCompilationUnit(this);
    }
}
