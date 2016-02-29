package de.uka.ilkd.keyabs.abs.expression;

import java.math.BigInteger;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSVisitor;

public class ABSIntLiteral extends ABSLiteralExp {

    private final BigInteger number;
    
    public ABSIntLiteral(BigInteger bigInt) {
	number = bigInt;
    }

    public ABSIntLiteral(int i) {
	number = BigInteger.valueOf(i);
    }

    @Override
    public void visit(ABSVisitor v) {
	v.performActionOnABSIntLiteral(this);
    }
    
    @Override
	public String toString() {
	return number.toString();
    }

    public BigInteger getValue() {
	return number;
    }
    
    
    /** tests if equals
     */
    @Override
	public boolean equalsModRenaming
        ( SourceElement o, NameAbstractionTable nat) {
        if (!(o instanceof ABSIntLiteral)) {
            return false;
        }
        return ((ABSIntLiteral)o).getValue().equals(getValue()); 
    }
    
    @Override
	public int hashCode(){
        int result = 17;
        result = 37 * result + getValue().hashCode();
        return result;
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
	return ((ABSServices)services).getTypeConverter().getABSIntType();
    }

}
