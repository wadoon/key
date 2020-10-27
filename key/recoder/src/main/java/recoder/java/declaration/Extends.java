package recoder.java.declaration;

import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

public class Extends extends InheritanceSpecification {
    private static final long serialVersionUID = 8407322782204527496L;

    public Extends() {
    }

    public Extends(TypeReference supertype) {
        super(supertype);
        makeParentRoleValid();
    }

    public Extends(ASTList<TypeReference> list) {
        super(list);
        makeParentRoleValid();
    }

    protected Extends(Extends proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Extends deepClone() {
        return new Extends(this);
    }

    public void accept(SourceVisitor v) {
        v.visitExtends(this);
    }
}
