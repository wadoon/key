package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSProgramElement;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSNullExp extends ABSProgramElement implements IABSPureExpression {

    @Override
    public int hashCode() {
        return 4711;
    }

    @Override
    public boolean equals(Object o) {
        return (o instanceof ABSNullExp);
    }
    
    /** commented in interface SourceElement. Overwrites the default
     * method implementation in ProgramElement by descending down to
     * the children.
     */
    @Override
	public boolean equalsModRenaming(SourceElement se, 
                                     NameAbstractionTable nat) {
        return this.equals(se);
    }
    

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSNullExp(this);
    }

    @Override
	public String toString() {
        return "null";
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        throw new RuntimeException("TODO");
    }

}
