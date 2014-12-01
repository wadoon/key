// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.FloatLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * Complete this class if you want to add support for the Java float type.
 *
 * At the moment this class contains only stubs.
 */
public final class FloatLDT extends LDT {

    public static final Name NAME = new Name("float");
    public static final Name FLOATLIT_NAME = new Name("FP");
    public static final Name NEGATIVE_LITERAL = new Name("negFloat");

    private final Function floatLit;
    private final Function neg;
    private final Function lessThan;
    private final Function greaterThan;
    private final Function javaAddFloat;

    public FloatLDT(TermServices services) {
	super(NAME, services);

	floatLit =	addFunction(services, FLOATLIT_NAME.toString());
	neg =		addFunction(services, NEGATIVE_LITERAL.toString());
	lessThan =	addFunction(services, "javaLtFloat");
	greaterThan =	addFunction(services, "javaGtFloat");
	javaAddFloat =	addFunction(services, "javaAddFloat");
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	                         Term[] subs,
	                         Services services,
	                         ExecutionContext ec) {
        if (subs.length == 1) {
            return isResponsible(op, subs[0], services, ec);
        } else if (subs.length == 2) {
            return isResponsible(op, subs[0], subs[1], services, ec);
        }
        return false;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	                         Term left,
	                         Term right,
	                         Services services,
	                         ExecutionContext ec) {
        if(left != null
           && left.sort().extendsTrans(targetSort())
           && right != null
           && right.sort().extendsTrans(targetSort())) {
            if(getFunctionFor(op, services, ec) != null) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	                         Term sub,
	                         TermServices services,
	                         ExecutionContext ec) {
        if(sub != null && sub.sort().extendsTrans(targetSort())) {
            if(op instanceof Negative) {
                return true;
            }
        }
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
	Debug.assertTrue(lit instanceof FloatLiteral,
	    "Literal '"+lit+"' is not a float literal.");

	String s = ((FloatLiteral)lit).getValue();
	IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();

	final boolean negative = (s.charAt(0) == '-');
	if (negative) {
	    s = s.substring(1);
	}

	//Remove last character which must be "f" for float literals
	s = s.substring(0, s.length()-1);
	String[] sp = s.split("\\.");

	Term intTerm, fractionTerm;


	//Use IntegerLDT to translate to Z notation, then remove the Z
	//Store the minus sign only in the integer part
	if (negative) {
	    intTerm = intLDT.translateLiteral(new IntLiteral("-" + sp[0]), services).sub(0);
	} else {
	    intTerm = intLDT.translateLiteral(new IntLiteral(sp[0]), services).sub(0);
	}

	fractionTerm = intLDT.translateLiteral(new IntLiteral(sp[1]), services).sub(0);

	return services.getTermFactory().createTerm(floatLit, intTerm, fractionTerm);
    }

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
	    			   Services services,
	    			   ExecutionContext ec) {
        if (op instanceof GreaterThan) {
            return getGreaterThan();
        } else if (op instanceof LessThan) {
            return getLessThan();
        } else if (op instanceof Plus) {
            return getJavaAddFloat();
        } else if (op instanceof Negative) {
            return getNeg();
        } else {
            return null;
        }
    }


    @Override
    public boolean hasLiteralFunction(Function f) {
	return containsFunction(f) && (f.arity()==0);
    }


    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
	if(!containsFunction((Function) t.op())) {
	    return null;
	}

	Function f = (Function)t.op();
	IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();

	if(f == floatLit) {
	    StringBuffer sb = new StringBuffer("");

	    //Use IntegerLDT to translate the Integer & Fraction to literals
	    IntLiteral il1 = (IntLiteral)intLDT.translateTerm(t.sub(0),
		children, services);
	    IntLiteral il2 = (IntLiteral)intLDT.translateTerm(t.sub(1),
		children, services);

	    sb.append(il1.getValue());
	    sb.append(".");
	    sb.append(il2.getValue());
	    sb.append("f");

	    return new FloatLiteral(sb.toString());
	}
	throw new RuntimeException("FloatLDT: Cannot convert term to program: "+t);
    }


    @Override
    public final Type getType(Term t) {
	if(t.sort() == targetSort()) {
	    return PrimitiveType.JAVA_FLOAT;
	} else {
	    return null;
	}
    }

    public Function getFloatSymbol() {
	return floatLit;
    }

    public Function getNeg() {
	return neg;
    }

    public Function getLessThan() {
	return lessThan;
    }

    public Function getGreaterThan() {
	return greaterThan;
    }

    public Function getJavaAddFloat() {
	return javaAddFloat;
    }
}
