package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;

public class ThisExpression extends ABSProgramElement implements
        IABSPureExpression {

    @Override
    public int hashCode() {
        return 4711;
    }

    @Override
    public boolean equals(Object o) {
        return (o instanceof ThisExpression);
    }

    /**
     * commented in interface SourceElement. Overwrites the default method
     * implementation in ProgramElement by descending down to the children.
     */
    @Override
    public boolean equalsModRenaming(SourceElement se, NameAbstractionTable nat) {
        return this.equals(se);
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return ec.getTypeReference().getKeYJavaType();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnThisExpression(this);
    }

}
