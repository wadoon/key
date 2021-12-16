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

import de.uka.ilkd.key.logic.op.Operator;
import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.DoubleLiteral;
import de.uka.ilkd.key.java.expression.literal.LongLiteral;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;

public final class DoubleLDT extends LDT implements IFloatingPointLDT {

    public static final Name NAME = new Name("double");
    public static final Name DOUBLELIT_NAME = new Name("DFP");
    public static final Name NEGATIVE_LITERAL = new Name("javaUnaryMinusDouble");

    private final Function doubleLit;
    private final Function lessThan;
    private final Function greaterThan;
    private final Function greaterOrEquals;
    private final Function lessOrEquals;

    private final Function eqDouble;

    private final Function javaUnaryMinusDouble;
    private final Function javaAddDouble;
    private final Function javaSubDouble;
    private final Function javaMulDouble;
    private final Function javaDivDouble;
    private final Function javaModDouble;

    private final Function javaMinDouble;
    private final Function javaMaxDouble;

    private final Function addDoubleIEEE;
    private final Function subDoubleIEEE;
    private final Function mulDoubleIEEE;
    private final Function divDoubleIEEE;
    private final Function doubleAbs;

    private final Function isNormal;
    private final Function isSubnormal;
    private final Function isNaN;
    private final Function isZero;
    private final Function isNice;
    private final Function isInfinite;
    private final Function isNegative;
    private final Function isPositive;

    private final Function roundingModeRNE;
    private final Function roundingModeRTN;
    private final Function roundingModeRTP;

    //Predicates that may not be abstracted, but only translated by SMT
    private final Function lessThan2;
    private final Function greaterThan2;
    private final Function greaterOrEquals2;
    private final Function lessOrEquals2;

    private final Function intervalMin;
    private final Function intervalMax;
    private final Function toInterval;

    private final Function sinDouble;
    private final Function cosDouble;
    private final Function acosDouble;
    private final Function asinDouble;
    private final Function tanDouble;
    private final Function atan2Double;
    private final Function sqrtDouble;
    private final Function powDouble;
    private final Function expDouble;
    private final Function atanDouble;

    public DoubleLDT(TermServices services) {
	super(NAME, services);

	doubleLit	      = addFunction(services, DOUBLELIT_NAME.toString());
	javaUnaryMinusDouble  = addFunction(services, NEGATIVE_LITERAL.toString());
	lessThan	    = addFunction(services, "javaLtDouble");
	greaterThan	    = addFunction(services, "javaGtDouble");
	lessOrEquals	    = addFunction(services, "javaLeqDouble");
	greaterOrEquals	    = addFunction(services, "javaGeqDouble");
	eqDouble		    = addFunction(services, "javaEqDouble");
	javaAddDouble	    = addFunction(services, "javaAddDouble");
	javaSubDouble	    = addFunction(services, "javaSubDouble");
	javaMulDouble	    = addFunction(services, "javaMulDouble");
	javaDivDouble	    = addFunction(services, "javaDivDouble");
	javaModDouble	    = addFunction(services, "javaModDouble");
	javaMaxDouble	    = addFunction(services, "javaMaxDouble");
	javaMinDouble	    = addFunction(services, "javaMinDouble");

	addDoubleIEEE	    = addFunction(services, "addDoubleIEEE");
	subDoubleIEEE	    = addFunction(services, "subDoubleIEEE");
	mulDoubleIEEE	    = addFunction(services, "mulDoubleIEEE");
	divDoubleIEEE	    = addFunction(services, "divDoubleIEEE");
	doubleAbs	    = addFunction(services, "doubleAbs");

	isNormal	    = addFunction(services, "doubleIsNormal");
	isSubnormal	    = addFunction(services, "doubleIsSubnormal");
	isNaN		    = addFunction(services, "doubleIsNaN");
	isZero		    = addFunction(services, "doubleIsZero");
	isNice		    = addFunction(services, "doubleIsNice");
	isInfinite	    = addFunction(services, "doubleIsInfinite");
	isPositive	    = addFunction(services, "doubleIsPositive");
	isNegative	    = addFunction(services, "doubleIsNegative");
	roundingModeRNE	    = addFunction(services, "RNE");
	roundingModeRTN	    = addFunction(services, "RTN");
	roundingModeRTP	    = addFunction(services, "RTP");

	lessThan2	    = addFunction(services, "interLtD");
	greaterThan2	    = addFunction(services, "interGtD");
	lessOrEquals2	    = addFunction(services, "interLeqD");
	greaterOrEquals2    = addFunction(services, "interGeqD");

	intervalMin	    = addFunction(services, "ivMinD");
	intervalMax	    = addFunction(services, "ivMaxD");
	toInterval	    = addFunction(services, "DTI");

	sinDouble       = addFunction(services, "sinDouble");
  cosDouble       = addFunction(services, "cosDouble");
  acosDouble       = addFunction(services, "acosDouble");
  asinDouble       = addFunction(services, "asinDouble");
  tanDouble       = addFunction(services, "tanDouble");
  atan2Double       = addFunction(services, "atan2Double");
  sqrtDouble       = addFunction(services, "sqrtDouble");
  powDouble       = addFunction(services, "powDouble");
  expDouble       = addFunction(services, "expDouble");
  atanDouble      = addFunction(services, "atanDouble");
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
   assert lit instanceof DoubleLiteral : "Literal '"+lit+"' is not a double literal.";
	String s = ((DoubleLiteral)lit).getValue();
	final boolean negative = (s.charAt(0) == '-');


	long doubleBits = Double.doubleToLongBits(Double.parseDouble(s));
        // String bitString = Long.toBinaryString(doubleBits);
        // long number = Long.parseLong(bitString, 2);
        long number = doubleBits;

	IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
	Term intTerm, fractionTerm;

        intTerm = services.getTermBuilder().zTerm(number).sub(0);

        // Set the second number to 0 for now
	fractionTerm = intLDT.translateLiteral(new LongLiteral(0), services).sub(0);

	return services.getTermFactory().createTerm(doubleLit, intTerm, fractionTerm);
    }


    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
	    			   Services services,
	    			   ExecutionContext ec) {
        if (op instanceof Negative) {
            return getJavaUnaryMinus();
        } else {
            return null;
        }
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
	return containsFunction(f) && (f.arity()==0);
    }

    private static boolean isNumberLiteral(Operator f) {
        char c = f.name().toString().charAt(0);
        return (c-'0'>=0) && (c-'0'<=9);
    }

    public long longBits(Term t, IntegerLDT integerLDT) {

        boolean neg = false;

        if (t.op() == doubleLit) {
            t = t.sub(0);
        }

        if (t.op() == integerLDT.getNegativeNumberSign()) {
            neg = true;
            t = t.sub(0);
        }

        StringBuffer sb = new StringBuffer("");
        while (isNumberLiteral(t.op())) {
            sb.append(t.op().name());
            t = t.sub(0);
        }
        // numbers must end with a sharp
        if (t.op() != integerLDT.getNumberTerminator()) {
            throw new NumberFormatException("Not supported: " + t);
        }

        if (neg) {
            sb.append("-");
        }

        sb.reverse();
        return Long.parseLong(sb.toString());

    }


    @Override
    public DoubleLiteral translateTerm(Term t, ExtList children, Services services) {
        Function f = (Function)t.op();
        IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();

        if(f == doubleLit) {
            String str = intLDT.toString(t.sub(0));
            long bits = Long.parseLong(str);
            Double d1 = Double.longBitsToDouble(bits);

            return new DoubleLiteral(d1.toString());
        }
        throw new RuntimeException("DoubleLDT: Cannot convert term to program: " + t);
    }


    @Override
    public final Type getType(Term t) {
	if(t.sort() == targetSort()) {
	    return PrimitiveType.JAVA_DOUBLE;
	} else {
	    return null;
	}
    }

    public Function getDoubleSymbol() {
	return doubleLit;
    }

    public Function getLessThan() {
	return lessThan;
    }

    public Function getGreaterThan() {
	return greaterThan;
    }

    public Function getLessOrEquals() {
	return lessOrEquals;
    }

    public Function getGreaterOrEquals() {
	return greaterOrEquals;
    }

    public Function getEquals() {
	return eqDouble;
    }

    public Function getJavaUnaryMinus() {
	return javaUnaryMinusDouble;
    }

    public Function getJavaAdd() {
	return javaAddDouble;
    }

    public Function getJavaSub() {
	return javaSubDouble;
    }

    public Function getJavaMul() {
	return javaMulDouble;
    }

    public Function getJavaDiv() {
	return javaDivDouble;
    }

    public Function getJavaMod() {
	return javaModDouble;
    }

    public Function getJavaMin() {
	return javaMinDouble;
    }

    public Function getJavaMax() {
	return javaMaxDouble;
    }

    public Function getIsNormal() {
	return isNormal;
    }

    public Function getIsSubnormal() {
	return isSubnormal;
    }

    public Function getIsNaN() {
	return isNaN;
    }

    public Function getIsZero() {
	return isZero;
    }

    @Override
    public Function getIsNice() {
        return isNice;
    }

    public Function getIsInfinite() {
	return isInfinite;
    }

    public Function getIsPositive() {
	return isPositive;
    }

    public Function getIsNegative() {
	return isNegative;
    }

    public Function getAddIEEE() {
	return addDoubleIEEE;
    }

    public Function getSubIEEE() {
	return subDoubleIEEE;
    }

    public Function getMulIEEE() {
	return mulDoubleIEEE;
    }

    public Function getDivIEEE() {
	return divDoubleIEEE;
    }

    public Function getAbs() {
	return doubleAbs;
    }

    public Function getRoundingModeRNE() {
	return roundingModeRNE;
    }

    @Override
    public Function getLiteralSymbol() {
        return getDoubleSymbol();
    }

    public Function getRoundingModeRTN() {
	return roundingModeRTN;
    }

    public Function getRoundingModeRTP() {
	return roundingModeRTP;
    }

    //Predicates that have been simplified as intervals
    public Function getLessThan2() {
	return lessThan2;
    }

    public Function getGreaterThan2() {
	return greaterThan2;
    }

    public Function getLessOrEquals2() {
	return lessOrEquals2;
    }

    public Function getGreaterOrEquals2() {
	return greaterOrEquals2;
    }

    public Function getIntervalMin() {
	return intervalMin;
    }

    public Function getIntervalMax() {
	return intervalMax;
    }

    public Function getToInterval() {
	return toInterval;
    }

    public Function getSinDouble() { return sinDouble; }

    public Function getCosDouble() { return cosDouble; }

    public Function getAcosDouble() { return acosDouble; }

    public Function getAsinDouble() { return asinDouble; }

    public Function getTanDouble() { return tanDouble; }

    public Function getAtan2Double() { return atan2Double; }

    public Function getSqrtDouble() { return sqrtDouble; }

    public Function getPowDouble() { return powDouble; }

    public Function getExpDouble() { return expDouble; }

    public Function getAtanDouble() {return atanDouble; }
}
