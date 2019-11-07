
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

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Helper class for sl-parsers dealing with Java's type promotion for floats and doubles.
 */
public class JavaFloatSemanticsHelper extends SemanticsHelper {

    private final TermBuilder tb;

    private final SLTranslationExceptionManager excManager;
    private final TypeConverter tc;
    private final FloatLDT floatLDT;
    private final DoubleLDT doubleLDT;
    private final Services services;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public JavaFloatSemanticsHelper(Services services,
                                    SLTranslationExceptionManager excManager) {
        assert services != null;
        assert excManager != null;

        this.services = services;
        this.excManager = excManager;
        this.tc = services.getTypeConverter();
        this.tb = services.getTermBuilder();
        this.floatLDT = services.getTypeConverter().getFloatLDT();
        this.doubleLDT = services.getTypeConverter().getDoubleLDT();
    }

    public static boolean hasFloatingPoint(SLExpression a, SLExpression b, Services services) {
        Sort floatSort = services.getTypeConverter().getFloatLDT().targetSort();
        Sort doubleSort = services.getTypeConverter().getDoubleLDT().targetSort();
        Sort aSort = a.getTerm().sort();
        Sort bSort = b.getTerm().sort();
        return aSort == floatSort || aSort == doubleSort || bSort == floatSort || bSort == doubleSort;
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private void raiseError(String message) throws SLTranslationException {
        throw excManager.createException(message);
    }

    private void raiseError(String message, Exception e) throws SLTranslationException {
        throw excManager.createException(message, e);
    }


    private KeYJavaType getPromotedType(SLExpression a, SLExpression b) {
        KeYJavaType result = tc.getPromotedType(a.getType(), b.getType());
        assert result != null;
        return result;
    }


    private KeYJavaType getPromotedType(SLExpression a) {
        KeYJavaType result = tc.getPromotedType(a.getType());
        assert result != null;
        return result;
    }

    private boolean isFloat(KeYJavaType resultType) {
        return resultType.getJavaType() == PrimitiveType.JAVA_FLOAT;
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    private Term promote(Term term, KeYJavaType targetType) {
        if(term.sort() == targetType.getSort()) {
            return term;
        } else {
            return tb.cast(targetType.getSort(), term);
        }
    }

    public SLExpression buildAddExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function add;
            if (isFloat(resultType))
                add = floatLDT.getJavaAdd();
            else add = doubleLDT.getJavaAdd();
            Term termA = promote(a.getTerm(), resultType);
            Term termB = promote(b.getTerm(), resultType);
            return new SLExpression(tb.func(add, termA, termB), resultType);
        } catch (RuntimeException e) {
            raiseError("Error in additive expression " + a + " + " + b + ":", e);
            return null; //unreachable
        }
    }

    public SLExpression buildEqualityExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType promotedType = getPromotedType(a, b);
            Function eq;
            if (isFloat(promotedType)) {
                eq = floatLDT.getEquals();
            } else eq = doubleLDT.getEquals();
            Term termA = promote(a.getTerm(), promotedType);
            Term termB = promote(b.getTerm(), promotedType);
            Term result = tb.func(eq, termA, termB);
            return new SLExpression(result);
        } catch (RuntimeException e) {
            raiseError("Error in equality expression " + a + " == " + b + ".", e);
            return null; //unreachable
        }
    }


    public SLExpression buildSubExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function sub;
            if (isFloat(resultType)) {
                sub = floatLDT.getJavaSub();
            } else sub = doubleLDT.getJavaSub();
            Term termA = promote(a.getTerm(), resultType);
            Term termB = promote(b.getTerm(), resultType);
            return new SLExpression(tb.func(sub, termA, termB), resultType);
        } catch (RuntimeException e) {
            raiseError("Error in subtract expression " + a + " - " + b + ".", e);
            return null; //unreachable
        }
    }


    //TODO this is not how it should be. Refactor, do fancy design patterns
    @Override
    public SLExpression buildUnsignedRightShiftExpression(SLExpression result, SLExpression e) {
        return null;
    }

    @Override
    public SLExpression buildRightShiftExpression(SLExpression a, SLExpression e) {
        return null;
    }

    @Override
    public SLExpression buildLeftShiftExpression(SLExpression result, SLExpression e) {
        return null;
    }

    public SLExpression buildMultExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function mul;
            if (isFloat(resultType))
                mul = floatLDT.getJavaMul();
            else mul = doubleLDT.getJavaMul();
            Term termA = promote(a.getTerm(), resultType);
            Term termB = promote(b.getTerm(), resultType);
            return new SLExpression(tb.func(mul, termA, termB), resultType);
        } catch (RuntimeException e) {
            raiseError("Error in multiplicative expression " + a + " * "
                    + b + ".", e);
            return null; //unreachable
        }
    }


    public SLExpression buildDivExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function div;
            if (isFloat(resultType))
                div = floatLDT.getJavaDiv();
            else
                div = doubleLDT.getJavaDiv();
            return new SLExpression(tb.func(div, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in division expression " + a + " / " + b + ".", e);
            return null; //unreachable
        }
    }

    public SLExpression buildUnaryMinusExpression(SLExpression a)
            throws SLTranslationException {
        assert a != null;
        try {
            KeYJavaType resultType = getPromotedType(a);
            Function minus;
            if (isFloat(resultType))
                minus = floatLDT.getJavaUnaryMinus();
            else
                minus = doubleLDT.getJavaUnaryMinus();
            Term termA = promote(a.getTerm(), resultType);
            return new SLExpression(tb.func(minus, termA), resultType);
        } catch (RuntimeException e) {
            raiseError("Error in unary minus expression -" + a + ".", e);
            return null; //unreachable
        }
    }

    public SLExpression buildModExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function mod;
            if (isFloat(resultType))
                mod = floatLDT.getJavaMod();
            else
                mod = doubleLDT.getJavaMod();
            return new SLExpression(tb.func(mod, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in modulo expression " + a + " / " + b + ".", e);
            return null; //unreachable
        }
    }

    public SLExpression buildPromotedUnaryPlusExpression(SLExpression a)
            throws SLTranslationException {
        return a;
    }

    //TODO(js)
//    public SLExpression buildCastExpression(KeYJavaType resultType,
//                                            SLExpression a)
//            throws SLTranslationException {
//        assert a != null;
//        try {
//            Function cast = floatLDT.getJavaCast(resultType.getJavaType());
//            if (cast != null)
//                return new SLExpression(tb.func(cast, a.getTerm()), resultType);
//            else { // there is no cast to \bigint
//                if (!isBigint(resultType))
//                    raiseError("Cannot cast expression " + a + " to " + resultType + ".");
//                return new SLExpression(a.getTerm(), resultType);
//            }
//        } catch (RuntimeException e) {
//            raiseError("Error in cast expression -" + a + ".", e);
//            return null; //unreachable
//        }
//    }
}
