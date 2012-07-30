package de.uka.ilkd.keyabs.abs.expression;

import java.math.BigInteger;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSProgramElement;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSIntLiteral extends ABSProgramElement implements IABSPureExpression {

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
    
    public String toString() {
	return number.toString();
    }

    public BigInteger getValue() {
	return number;
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
	return ((ABSServices)services).getTypeConverter().getABSIntType();
    }

}
