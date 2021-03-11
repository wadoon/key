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

package de.uka.ilkd.key.smt;


import java.math.BigDecimal;
import java.math.BigInteger;

import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.smt.newsmt2.FloatHandler;
import de.uka.ilkd.key.smt.newsmt2.SExpr;
import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.DoubleLiteral;
import de.uka.ilkd.key.java.expression.literal.FloatLiteral;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.util.Debug;

/**
 * Translates a number into a string representation.
 */
public final class NumberTranslation {

    private NumberTranslation() {}

    /** This methods translates a term with sort "numbers" into a
     * BigInteger representing the number. 
     * 
     * @param term term with sort "numbers"
     * @return An instance of BigInteger representing the number
    */
    public static BigInteger translate(Term term) {
	if (!term.sort().name().toString().trim().equals("numbers")) {
	    throw new IllegalArgumentException
		("Only terms with sort \"numbers\" may be translated.\n"+
		 "Term "+term+" is  of sort "+term.sort().name().toString().trim());
	}
	Operator op = term.op();
	String name = op.name().toString();
	if (name.length() == 1) {
	    char ch = name.charAt(0);
	    if (ch >= '0' && ch <= '9') {
		Debug.assertTrue(term.arity() == 1);
		return translate(term.sub(0))
		    .multiply(smallInts[10])
		    .add(smallInts[ch - '0']);
	    } else if (ch == '#') {
		Debug.assertTrue(term.arity() == 0);
		return BigInteger.ZERO;
	    } else {
		Debug.fail("unknown number literal");
		return null; // not reached
	    }
	} else if ("neglit".equals(name)) {
	    Debug.assertTrue(term.arity() == 1);
	    /* Hint: translate operator "neg" at all places
	     * correctly, e.g. neg(1(neg(1(#)))). */
	    return translate(term.sub(0)).negate();
	} else {
	    Debug.fail("unknown number literal");
	    return null; // not reached
	}
    }

    /* BigInteger instances for values 0..10 */
    private static final BigInteger[] smallInts;

    static {
	/* initialize smallInts */
	smallInts = new BigInteger[11];
	for (int i = 0; i < smallInts.length; ++i) {
	    smallInts[i] = new BigInteger("" + i);
	}
    }

    /** Translate a float literal of sort "float" in FP notation to
     * an SMTLIB fp literal
     *
     * @param term an application of FP
     * @return A string containing the translated literal
     */
    public static SExpr translateFloatToSMTLIB(Term term, Services services) {

		long repr = intFromTerm(term.sub(0), services);
		assert repr <= 0xffff_ffffL;

		String sign = "#b" + extractBits(repr, 31, 1);
		String exp = "#b" + extractBits(repr, 23, 8);
		String mantissa = "#b" + extractBits(repr, 0, 23);

		SExpr result = new SExpr("fp", FloatHandler.FLOAT, sign, exp, mantissa);
		return result;
	}

	private static long intFromTerm(Term term, Services services) {
		if(term.op() == services.getTypeConverter().getIntegerLDT().getNumberTerminator()) {
			return 0L;
		} else {
			int digit = Integer.parseInt(term.op().name().toString());
			return 10 * intFromTerm(term.sub(0), services) + digit;
		}
	}

	/** Translate a double literal of sort "double" in DFP notation to
	 * an SMTLIB fp literal
	 *
	 * @param term an application of DFP
	 * @return An sexpr containing the translated literal
	 */
	public static SExpr translateDoubleToSMTLIB(Term term, Services services) {

		long repr = intFromTerm(term.sub(0), services);

		String sign = "#b" + extractBits(repr, 63, 1);
		String exp = "#b" + extractBits(repr, 52, 11);
		String mantissa = "#b" + extractBits(repr, 0, 52);

		SExpr result = new SExpr("fp", sign, exp, mantissa);
		return result;
	}

	private static String extractBits(long value, int fromBit, int count) {
		StringBuilder sb = new StringBuilder();
		value = value >>> fromBit;
		for (int i = 0; i < count; i++) {
			sb.insert(0, (value & 1) == 1 ? "1" : "0");
			value >>>= 1;
		}
		return sb.toString();
	}


}
