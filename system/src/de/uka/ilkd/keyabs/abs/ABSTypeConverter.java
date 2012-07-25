package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.AbstractTypeConverter;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;
import de.uka.ilkd.keyabs.logic.ldt.HistoryLDT;

public final class ABSTypeConverter extends AbstractTypeConverter {
    
    private HistoryLDT historyLDT;
    
    public ABSTypeConverter(ABSServices services) {
        super(services);
    }

    public void init(LDT ldt) {     
        if (ldt instanceof HistoryLDT) {
            historyLDT = (HistoryLDT) ldt;
        }
        super.init(ldt);
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
        } else if (pe instanceof ABSBinaryOperatorPureExp) {
            Term left = convertToLogicElement(((ABSBinaryOperatorPureExp) pe).getChildAt(0), ec);
            Term right = convertToLogicElement(((ABSBinaryOperatorPureExp) pe).getChildAt(1), ec);
            
            if (pe instanceof ABSAddExp) {
                return getServices().getTermBuilder().add(services, left, right);
            } else if (pe instanceof ABSMultExp) {
                return getServices().getTermBuilder().mul(services, left, right);                
            } else if (pe instanceof ABSAndBoolExp) {
            	
            } else if (pe instanceof ABSOrBoolExp) {
            }
        } else if (pe instanceof ABSNullExp) {
        	return getServices().getTermBuilder().NULL(getServices());
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
    public boolean isIntegerType(Type t) {
        Type type = t;
    	if (t instanceof KeYJavaType) {
        	return ((KeYJavaType) t).getSort().extendsTrans(getIntegerLDT().targetSort());
        }
    	return type instanceof ABSInterfaceType;
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
        Type type = t;
    	if (t instanceof KeYJavaType) {
        	type = ((KeYJavaType) t).getJavaType();
        }
    	return type instanceof ABSInterfaceType;
    }

    @Override
    public KeYJavaType getBooleanType() {
        return services.getProgramInfo().getTypeByName("ABS.StdLib.Bool");
    }

    public KeYJavaType getABSIntType() {
        return services.getProgramInfo().getTypeByName("ABS.StdLib.Int");
    }

    public HistoryLDT getHistoryLDT() {
        return historyLDT;
    }


}
