package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.AbstractTypeConverter;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;
import de.uka.ilkd.keyabs.abs.expression.*;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;
import de.uka.ilkd.keyabs.logic.ldt.HeapLDT;
import de.uka.ilkd.keyabs.logic.ldt.HistoryLDT;

public final class ABSTypeConverter extends AbstractTypeConverter<ABSServices> {

    private HistoryLDT historyLDT;

    public ABSTypeConverter(ABSServices services) {
	super(services);
    }

    @Override
    public void init(LDT ldt) {
	if (ldt instanceof HistoryLDT) {
	    historyLDT = (HistoryLDT) ldt;
	}
	super.init(ldt);
    }

    @Override
    public Term convertToLogicElement(ProgramElement pe) {
	return convertToLogicElement(pe, getServices().getProgramInfo()
		.getDefaultExecutionContext());
    }

    @Override
    public Term convertToLogicElement(ProgramElement pe, ExecutionContext ec) {
	if (pe instanceof IntLiteral) {
	    return getIntegerLDT().translateLiteral((IntLiteral) pe,
		    getServices());
	} else {
	    ABSTermBuilder TB = getServices().getTermBuilder();
	    if (pe instanceof IABSLocationReference) {
		    if (pe instanceof IABSFieldReference) {
                IABSFieldReference field = (IABSFieldReference) pe;
                return TB.dot(services, field.getVariable().sort(),
                        TB.func(getThisConstant()),
                        getHeapLDT().getFieldSymbolForPV((LocationVariable) field.getVariable(),services));
            } else {
		        return TB.var(((IABSLocationReference) pe).getVariable());
            }
        } /*else if (pe instanceof MethodName) {
		return TB.func((Function) getServices().getNamespaces()
			.functions().lookup((Name) pe));
	    }*/ else if (pe instanceof IProgramVariable) {
            if (pe instanceof LocationVariable && ((LocationVariable)pe).isMember()) {
                LocationVariable field = (LocationVariable) pe;
                return TB.dot(services, field.sort(),
                        TB.func(getThisConstant()),
                        getHeapLDT().getFieldSymbolForPV(field, services));
            } else {
                return TB.var((IProgramVariable) pe);
            }

        } else if (pe instanceof ABSMethodLabel) {
            return TB.func(((ABSMethodLabel)pe).getMethodLabel());
        } else {
		final TermBuilder tb = services.getTermBuilder();
		if (pe instanceof ABSBinaryOperatorPureExp) {
		    Term left = convertToLogicElement(
			    ((ABSBinaryOperatorPureExp) pe).getChildAt(0), ec);
		    Term right = convertToLogicElement(
			    ((ABSBinaryOperatorPureExp) pe).getChildAt(1), ec);

		    if (pe instanceof ABSAddExp) {
			return TB.add(services, left, right);
		    } else if (pe instanceof ABSMultExp) {
			return TB.mul(services, left, right);
		    } else if (pe instanceof ABSAndBoolExp) {
			return convertBool2Fml(Junctor.AND, left, right);
		    } else if (pe instanceof ABSOrBoolExp) {
			return convertBool2Fml(Junctor.OR, left, right);
		    } else if (pe instanceof ABSEqExp) {
			return tb.equals(left, right);
		    } else if (pe instanceof ABSNotEqExp) {
			return tb.not(tb.equals(left, right));
		    } else if (pe instanceof ABSGEQExp) {
			return tb.geq(left, right, services);
		    } else if (pe instanceof ABSGTExp) {
			return tb.gt(left, right, services);
		    } else if (pe instanceof ABSLEQExp) {
			return tb.leq(left, right, services);
		    } else if (pe instanceof ABSLTExp) {
			return tb.lt(left, right, services);
		    }
		} else if (pe instanceof ABSNullExp) {
		    return TB.NULL(getServices());
		} else if (pe instanceof ABSDataConstructorExp) {
		    ABSDataConstructorExp dtCons = (ABSDataConstructorExp) pe;
		    Function cons = (Function) services.getNamespaces()
			    .functions().lookup((Name) dtCons.getChildAt(0));
		    Term[] subs = new Term[dtCons.getArgumentCount()];
		    for (int i = 0; i < dtCons.getArgumentCount(); i++) {
			subs[i] = convertToLogicElement(
				dtCons.getArgumentAt(i), ec);
		    }
		    return tb.func(cons, subs);
		} else if (pe instanceof ABSIntLiteral) {
		    return tb.zTerm(services, ((ABSIntLiteral) pe).getValue()
			    .toString());
		} else if (pe instanceof ABSMinusExp) {
		    return tb.mul(
			    services,
			    tb.zTerm(services, "-1"),
			    convertToLogicElement(
				    ((ABSMinusExp) pe).getChildAt(0), ec));
		} else if (pe instanceof ThisExpression) {
            return tb.func(getThisConstant());
        } else if (pe instanceof ABSFnApp) {
            ABSFnApp fnApp = (ABSFnApp) pe;
            Function fn = (Function) services.getNamespaces().functions().lookup(fnApp.getFnName());
            Term[] args = new Term[fnApp.getArgumentCount()];
            for (int i = 0; i<fnApp.getArgumentCount(); i++) {
                IABSPureExpression arg = fnApp.getArgumentAt(i);
                args[i] = convertToLogicElement(arg);
            }
            return tb.func(fn, args);
        } else {
            System.out.println("Unsupported " + pe + ":" + pe.getClass());
        }
	    }
	}
	return null;
    }

    private Function getThisConstant() {
        return (Function) services.getNamespaces().functions().lookup(new Name("this"));
    }

    private Term convertBool2Fml(Junctor op, Term left, Term right) {
	TermBuilder tb = services.getTermBuilder();
	Term leftFml = left.sort() == Sort.FORMULA ? left : tb.equals(left,
		tb.TRUE(services));
	Term rightFml = right.sort() == Sort.FORMULA ? right : tb.equals(right,
		tb.TRUE(services));

	return tb.ife(tb.tf().createTerm(op, leftFml, rightFml),
		tb.TRUE(services), tb.FALSE(services));
    }

    @Override
    public ABSTypeConverter copy(ABSServices services) {
	final ABSTypeConverter tc = new ABSTypeConverter((ABSServices) services);
	tc.init(models);
	return tc;
    }

    @Override
    public KeYJavaType getPromotedType(KeYJavaType keYJavaType) {
	// TODO Auto-generated method stub
	return null;
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
	    return ((KeYJavaType) t).getSort().extendsTrans(
		    getIntegerLDT().targetSort());
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

    public HeapLDT getHeapLDT() {
	return (HeapLDT) heapLDT;
    }

}
