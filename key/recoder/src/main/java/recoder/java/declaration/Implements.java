package recoder.java.declaration;

import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

public class Implements extends InheritanceSpecification {
    private static final long serialVersionUID = 8977810702311137411L;

    public Implements() {
    }

    public Implements(TypeReference supertype) {
        super(supertype);
        makeParentRoleValid();
    }

    public Implements(ASTList<TypeReference> list) {
        super(list);
        makeParentRoleValid();
    }

    protected Implements(Implements proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Implements deepClone() {
        return new Implements(this);
    }

    public void accept(SourceVisitor v) {
        v.visitImplements(this);
    }
}
