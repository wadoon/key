package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.AbstractTypeConverter;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class ABSTypeConverter extends AbstractTypeConverter {

    
    public ABSTypeConverter(ABSServices services) {
        super(services);
    }

    @Override
    public Term convertToLogicElement(ProgramElement pe) {
        return convertToLogicElement(pe, getServices().getProgramInfo().getDefaultExecutionContext());
    }

    @Override
    public Term convertToLogicElement(ProgramElement pe, ExecutionContext ec) {
        if (pe instanceof IntLiteral) {
            return getIntegerLDT().translateLiteral((IntLiteral) pe, getServices());
        } else if (pe instanceof IABSLocationReference) {
            return getServices().getTermBuilder().var(((IABSLocationReference)pe).getVariable());
        } else if (pe instanceof IProgramVariable) {
            return getServices().getTermBuilder().var((IProgramVariable)pe);
        }
        return null;
    }

    @Override
    public ABSTypeConverter copy(IServices services) {
        final ABSTypeConverter tc = new ABSTypeConverter(getServices());
        tc.init(models);
        return tc;
    }

    @Override
    public KeYJavaType getPromotedType(KeYJavaType keYJavaType) {
        // TODO Auto-generated method stub
        return null;
    }

    public ABSServices getServices() {
        return (ABSServices) super.getServices();
    }

    @Override
    public boolean isArithmeticType(Type t) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isAssignableTo(Expression expr, Type to, ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isAssignableTo(Type from, Type to) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isBooleanType(Type t) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isCastingTo(Type from, Type to) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isIdentical(Type from, Type to) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isIntegerType(Type t2) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isIntegralType(Type t) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isNullType(Type t) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isReferenceType(Type t) {
        // TODO Auto-generated method stub
        return false;
    }

}
