// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.common.core.theories;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.factories.CCTermBuilder;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.services.TermServices;

/**
 * Theory of Integers, Shorts and Bytes.
 *
 * @author Dominic Scheurer
 */
public class CCIntegerTheory<T extends CCTerm<?, ?, ?, T>> extends CCTheory {

    public static final Name NAME = new Name("int");

    // public name constants
    public static final String NEGATIVE_LITERAL_STRING = "neglit";
    public static final Name NUMBERS_NAME = new Name("Z");
    public static final Name CHAR_ID_NAME = new Name("C");

    // the following fields cache the symbols from integerHeader.key.
    // (explanations see there)
    private final Function sharp;
    private final Function numberSymbol[] = new Function[10];
    private final Function neglit;
    private final Function numbers;
    private final Function charID;
    private final Function add;
    private final Function neg;
    private final Function sub;
    private final Function mul;
    private final Function div;
    private final Function mod;
    private final Function pow;
    private final Function bsum;
    private final Function bprod;
    private final Function jdiv;
    private final Function jmod;
    private final Function addJint;
    private final Function moduloByte;
    private final Function moduloShort;
    private final Function moduloInt;
    private final Function moduloChar;
    private final Function javaUnaryMinusInt;
    private final Function javaUnaryMinusLong;
    private final Function javaBitwiseNegation;
    private final Function javaAddInt;
    private final Function javaAddLong;
    private final Function javaSubInt;
    private final Function javaSubLong;
    private final Function javaMulInt;
    private final Function javaMulLong;
    private final Function javaMod;
    private final Function javaDivInt;
    private final Function javaDivLong;
    private final Function javaShiftRightInt;
    private final Function javaShiftRightLong;
    private final Function javaShiftLeftInt;
    private final Function javaShiftLeftLong;
    private final Function javaUnsignedShiftRightInt;
    private final Function javaUnsignedShiftRightLong;
    private final Function javaBitwiseOrInt;
    private final Function javaBitwiseOrLong;
    private final Function javaBitwiseAndInt;
    private final Function javaBitwiseAndLong;
    private final Function javaBitwiseXOrInt;
    private final Function javaBitwiseXOrLong;
    private final Function javaCastByte;
    private final Function javaCastShort;
    private final Function javaCastInt;
    private final Function javaCastLong;
    private final Function javaCastChar;
    private final Function lessThan;
    private final Function greaterThan;
    private final Function greaterOrEquals;
    private final Function lessOrEquals;
    private final Function index;
    private final T one;
    private final T zero;
    
    @SuppressWarnings("unused")
    private final Function unaryMinusJint;
    @SuppressWarnings("unused")
    private final Function unaryMinusJlong;
    @SuppressWarnings("unused")
    private final Function addJlong;
    @SuppressWarnings("unused")
    private final Function subJint;
    @SuppressWarnings("unused")
    private final Function subJlong;
    @SuppressWarnings("unused")
    private final Function mulJint;
    @SuppressWarnings("unused")
    private final Function mulJlong;
    @SuppressWarnings("unused")
    private final Function modJint;
    private final Function modJlong;
    @SuppressWarnings("unused")
    private final Function divJint;
    @SuppressWarnings("unused")
    private final Function divJlong;
    @SuppressWarnings("unused")
    private final Function shiftright;
    @SuppressWarnings("unused")
    private final Function shiftleft;
    @SuppressWarnings("unused")
    private final Function shiftrightJint;
    @SuppressWarnings("unused")
    private final Function shiftrightJlong;
    @SuppressWarnings("unused")
    private final Function shiftleftJint;
    @SuppressWarnings("unused")
    private final Function shiftleftJlong;
    @SuppressWarnings("unused")
    private final Function unsignedshiftrightJint;
    @SuppressWarnings("unused")
    private final Function unsignedshiftrightJlong;
    @SuppressWarnings("unused")
    private final Function binaryOr;
    @SuppressWarnings("unused")
    private final Function binaryXOr;
    @SuppressWarnings("unused")
    private final Function binaryAnd;
    private final Function orJint;
    @SuppressWarnings("unused")
    private final Function orJlong;
    @SuppressWarnings("unused")
    private final Function andJint;
    @SuppressWarnings("unused")
    private final Function andJlong;
    @SuppressWarnings("unused")
    private final Function xorJint;
    @SuppressWarnings("unused")
    private final Function xorJlong;
    @SuppressWarnings("unused")
    private final Function moduloLong;
    @SuppressWarnings("unused")
    private final Function inByte;
    @SuppressWarnings("unused")
    private final Function inShort;
    @SuppressWarnings("unused")
    private final Function inInt;
    @SuppressWarnings("unused")
    private final Function inLong;
    @SuppressWarnings("unused")
    private final Function inChar;

    /**
     * TODO: Document.
     *
     * @param name
     * @param services
     */
    protected CCIntegerTheory(TermServices<?, T, ?, ?> services) {
        super(NAME, services);

        // Initialize caches for function symbols from integerHeader.key
        sharp = addFunction(services, "#");
        for (int i = 0; i < 10; i++) {
            numberSymbol[i] = addFunction(services, "" + i);
        }
        neglit = addFunction(services, NEGATIVE_LITERAL_STRING);
        numbers = addFunction(services, NUMBERS_NAME.toString());

        assert sharp.sort() == numbers.argSort(0);

        charID = addFunction(services, CHAR_ID_NAME.toString());
        add = addFunction(services, "add");
        neg = addFunction(services, "neg");
        sub = addFunction(services, "sub");
        mul = addFunction(services, "mul");
        div = addFunction(services, "div");
        mod = addFunction(services, "mod");
        bsum = addFunction(services, "bsum");
        bprod = addFunction(services, "bprod");
        jdiv = addFunction(services, "jdiv");
        jmod = addFunction(services, "jmod");
        pow = addFunction(services, "pow");
        unaryMinusJint = addFunction(services, "unaryMinusJint");
        unaryMinusJlong = addFunction(services, "unaryMinusJlong");
        addJint = addFunction(services, "addJint");
        addJlong = addFunction(services, "addJlong");
        subJint = addFunction(services, "subJint");
        subJlong = addFunction(services, "subJlong");
        mulJint = addFunction(services, "mulJint");
        mulJlong = addFunction(services, "mulJlong");
        modJint = addFunction(services, "modJint");
        modJlong = addFunction(services, "modJlong");
        divJint = addFunction(services, "divJint");
        divJlong = addFunction(services, "divJlong");

        shiftright = addFunction(services, "shiftright");
        shiftleft = addFunction(services, "shiftleft");
        shiftrightJint = addFunction(services, "shiftrightJint");
        shiftrightJlong = addFunction(services, "shiftrightJlong");
        shiftleftJint = addFunction(services, "shiftleftJint");
        shiftleftJlong = addFunction(services, "shiftleftJlong");
        unsignedshiftrightJint =
                addFunction(services, "unsignedshiftrightJint");
        unsignedshiftrightJlong =
                addFunction(services, "unsignedshiftrightJlong");
        binaryOr = addFunction(services, "binaryOr");
        binaryAnd = addFunction(services, "binaryAnd");
        binaryXOr = addFunction(services, "binaryXOr");
        orJint = addFunction(services, "orJint");
        orJlong = addFunction(services, "orJlong");
        andJint = addFunction(services, "andJint");
        andJlong = addFunction(services, "andJlong");
        xorJint = addFunction(services, "xorJint");
        xorJlong = addFunction(services, "xorJlong");
        moduloByte = addFunction(services, "moduloByte");
        moduloShort = addFunction(services, "moduloShort");
        moduloInt = addFunction(services, "moduloInt");
        moduloLong = addFunction(services, "moduloLong");
        moduloChar = addFunction(services, "moduloChar");
        javaUnaryMinusInt = addFunction(services, "javaUnaryMinusInt");
        javaUnaryMinusLong = addFunction(services, "javaUnaryMinusLong");
        javaBitwiseNegation = addFunction(services, "javaBitwiseNegation");
        javaAddInt = addFunction(services, "javaAddInt");
        javaAddLong = addFunction(services, "javaAddLong");
        javaSubInt = addFunction(services, "javaSubInt");
        javaSubLong = addFunction(services, "javaSubLong");
        javaMulInt = addFunction(services, "javaMulInt");
        javaMulLong = addFunction(services, "javaMulLong");
        javaMod = addFunction(services, "javaMod");
        javaDivInt = addFunction(services, "javaDivInt");
        javaDivLong = addFunction(services, "javaDivLong");
        javaShiftRightInt = addFunction(services, "javaShiftRightInt");
        javaShiftRightLong = addFunction(services, "javaShiftRightLong");
        javaShiftLeftInt = addFunction(services, "javaShiftLeftInt");
        javaShiftLeftLong = addFunction(services, "javaShiftLeftLong");
        javaUnsignedShiftRightInt =
                addFunction(services, "javaUnsignedShiftRightInt");
        javaUnsignedShiftRightLong =
                addFunction(services, "javaUnsignedShiftRightLong");
        javaBitwiseOrInt = addFunction(services, "javaBitwiseOrInt");
        javaBitwiseOrLong = addFunction(services, "javaBitwiseOrLong");
        javaBitwiseAndInt = addFunction(services, "javaBitwiseAndInt");
        javaBitwiseAndLong = addFunction(services, "javaBitwiseAndLong");
        javaBitwiseXOrInt = addFunction(services, "javaBitwiseXOrInt");
        javaBitwiseXOrLong = addFunction(services, "javaBitwiseXOrLong");
        javaCastByte = addFunction(services, "javaCastByte");
        javaCastShort = addFunction(services, "javaCastShort");
        javaCastInt = addFunction(services, "javaCastInt");
        javaCastLong = addFunction(services, "javaCastLong");
        javaCastChar = addFunction(services, "javaCastChar");
        lessThan = addFunction(services, "lt");
        greaterThan = addFunction(services, "gt");
        greaterOrEquals = addFunction(services, "geq");
        lessOrEquals = addFunction(services, "leq");
        inByte = addFunction(services, "inByte");
        inShort = addFunction(services, "inShort");
        inInt = addFunction(services, "inInt");
        inLong = addFunction(services, "inLong");
        inChar = addFunction(services, "inChar");
        index = addFunction(services, "index");

        // cache often used constants
        CCTermBuilder<?, T> tb = services.getTermBuilder();
        zero = tb.func(numbers, tb.func(numberSymbol[0], tb.func(sharp)));
        one = tb.func(numbers, tb.func(numberSymbol[1], tb.func(sharp)));
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public Function getNumberTerminator() {
        return sharp;
    }

    public Function getNumberLiteralFor(int number) {
        if (number < 0 || number > 9) {
            throw new IllegalArgumentException(
                    "Number literal symbols range from 0 to 9. Requested was:"
                            + number);
        }

        return numberSymbol[number];
    }

    public Function getNegativeNumberSign() {
        return neglit;
    }

    public Function getNumberSymbol() {
        return numbers;
    }

    public Function getCharSymbol() {
        return charID;
    }

    public Function getAdd() {
        return add;
    }

    public Function getNeg() {
        return neg;
    }

    public Function getSub() {
        return sub;
    }

    public Function getMul() {
        return mul;
    }

    public Function getDiv() {
        return div;
    }

    public Function getMod() {
        return mod;
    }

    public Function getPow() {
        return pow;
    }

    public Function getBsum() {
        return bsum;
    }

    public Function getBprod() {
        return bprod;
    }

    public Function getLessThan() {
        return lessThan;
    }

    public Function getGreaterThan() {
        return greaterThan;
    }

    public Function getGreaterOrEquals() {
        return greaterOrEquals;
    }

    public Function getLessOrEquals() {
        return lessOrEquals;
    }

    /**
     * Placeholder for the loop index variable in an enhanced for loop over
     * arrays. Follows the proposal by David Cok to adapt JML to Java5.
     * 
     * @return
     */
    public Function getIndex() {
        return index;
    }

    /**
     * returns the function symbol used to represent java-like division of the
     * arithmetical integers
     * 
     * @return the function symbol used to represent integer division
     */
    public Function getJDivision() {
        return jdiv;
    }

    /**
     * returns the function symbol used to represent the modulo operation of the
     * arithmetical integers
     * 
     * @return the function symbol used to represent the integer modulo
     *         operation
     */
    public Function getArithModulo() {
        return mod;
    }

    /**
     * returns the function symbol used to represent the java-like modulo
     * operation of the arithmetical integers
     * 
     * @return the function symbol used to represent the integer modulo
     *         operation
     */
    public Function getJModulo() {
        return jmod;
    }

    /**
     * returns a function mapping an arithmetic integer to its Java long
     * representation
     */
    public Function getModuloLong() {
        return modJlong;
    }

    /** maps an integer back into long range */
    public Function getArithModuloLong() {
        return modJlong;
    }

    /** maps an integer back into int range */
    public Function getArithModuloInt() {
        return moduloInt;
    }

    /** maps an integer back into long range */
    public Function getArithModuloShort() {
        return moduloShort;
    }

    /** maps an integer back into byte range */
    public Function getArithModuloByte() {
        return moduloByte;
    }

    /** maps an integer back into char range */
    public Function getArithModuloChar() {
        return moduloChar;
    }

    /**
     * returns the function symbol interpreted as the Java addition on int (or
     * promotabel to int) operators, i.e. this addition performs a modulo
     * operation wrt. to the range of type <code>int</code>. This function is
     * independent of the chosen integer semantics.
     * 
     * In case you want to represent the Java addition on operands promotable to
     * <code>int</code> which shall be interpreted by the chosen integer
     * semantics use {@link IntegerLDT#getJavaAddInt()} instead
     * 
     * @return mathematical interpreted function realising the Java addition on
     *         operands of or promotable to type <code>int</code>
     */
    public Function getArithJavaIntAddition() {
        return addJint;
    }

    /**
     * returns the function symbol representing the bitwise-or for Java int
     */
    public Function getBitwiseOrJavaInt() {
        return orJint;
    }

    /**
     * the function representing the Java operator when one of the operators is
     * an or can be promoted to an int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaAddInt() {
        return javaAddInt;
    }

    /**
     * the function representing the Java operator when one of the operators is
     * of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaAddLong() {
        return javaAddLong;
    }

    /**
     * the function representing the Java operator when one of the operators is
     * an or can be promoted to int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseAndInt() {
        return javaBitwiseAndInt;
    }

    /**
     * the function representing the Java operator when one of the operators is
     * of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseAndLong() {
        return javaBitwiseAndLong;
    }

    /**
     * the function representing the Java operator <code>~</code>
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseNegation() {
        return javaBitwiseNegation;
    }

    /**
     * the function representing the Java operator <code>|</code> when one of
     * the operands is an or can be promoted to int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseOrInt() {
        return javaBitwiseOrInt;
    }

    /**
     * the function representing the Java operator <code>|</code> when one of
     * the operands is of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseOrLong() {
        return javaBitwiseOrLong;
    }

    /**
     * the function representing the Java operator <code>^</code> when one of
     * the operands is an or can be promoted to int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseXOrInt() {
        return javaBitwiseXOrInt;
    }

    /**
     * the function representing the Java operator <code>^</code> when one of
     * the operands is exact of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaBitwiseXOrLong() {
        return javaBitwiseXOrLong;
    }

    /**
     * the function representing the Java operator <code>(byte)</code>
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastByte() {
        return javaCastByte;
    }

    /**
     * the function representing the Java operator <code>(char)</code>
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastChar() {
        return javaCastChar;
    }

    /**
     * the function representing the Java operator <code>(int)</code>
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastInt() {
        return javaCastInt;
    }

    /**
     * the function representing the Java operator <code>(long)</code>
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastLong() {
        return javaCastLong;
    }

    /**
     * the function representing the Java operator <code>(short)</code>
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastShort() {
        return javaCastShort;
    }

    /**
     * the function representing the Java operator <code>/</code> when one of
     * the operands is an or a subtype of int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaDivInt() {
        return javaDivInt;
    }

    /**
     * the function representing the Java operator <code>/</code> when one of
     * the operands is exact of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaDivLong() {
        return javaDivLong;
    }

    /**
     * the function representing the Java operator <code>%</code> when one of
     * the operands is an or a subtype of int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaMod() {
        return javaMod;
    }

    /**
     * the function representing the Java operator <code>*</code> when one of
     * the operands is an or a subtype of int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaMulInt() {
        return javaMulInt;
    }

    /**
     * the function representing the Java operator <code>*</code> when one of
     * the operands is exact of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaMulLong() {
        return javaMulLong;
    }

    /**
     * the function representing the Java operator <code>&lt;&lt;</code> when
     * one of the operands is an or a subtype of int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaShiftLeftInt() {
        return javaShiftLeftInt;
    }

    /**
     * the function representing the Java operator <code>&lt;&lt;</code> when
     * one of the operands is exact of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaShiftLeftLong() {
        return javaShiftLeftLong;
    }

    /**
     * the function representing the Java operator <code>&gt;&gt;</code> when
     * one of the operands is an or a subtype of int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaShiftRightInt() {
        return javaShiftRightInt;
    }

    /**
     * the function representing the Java operator <code>&gt;&gt;</code> when
     * one of the operands is exact of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaShiftRightLong() {
        return javaShiftRightLong;
    }

    /**
     * the function representing the Java operator <code>-</code> when one of
     * the operands is an or a subtype of int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaSubInt() {
        return javaSubInt;
    }

    /**
     * the function representing the Java operator <code>-</code> when one of
     * the operands is exact of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaSubLong() {
        return javaSubLong;
    }

    /**
     * the function representing the Java operator <code>-expr</code> when one
     * of the operands is an or a subtype of int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaUnaryMinusInt() {
        return javaUnaryMinusInt;
    }

    /**
     * the function representing the Java operator <code>-exprLong</code> when
     * one of the operands is exact of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaUnaryMinusLong() {
        return javaUnaryMinusLong;
    }

    /**
     * the function representing the Java operator <code>&gt;&gt;&gt;</code>
     * when one of the operands is an or a subtype of int
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaUnsignedShiftRightInt() {
        return javaUnsignedShiftRightInt;
    }

    /**
     * the function representing the Java operator <code>&gt;&gt;&gt;</code>
     * when one of the operands is exact of type long
     * 
     * @return function representing the generic Java operator function
     */
    public Function getJavaUnsignedShiftRightLong() {
        return javaUnsignedShiftRightLong;
    }

    public T zero() {
        return zero;
    }

    public T one() {
        return one;
    }
    
    public T toZTerm(String intStr, TermServices<?, T, ?, ?> services) {
        int length = 0;
        boolean minusFlag = false;

        char[] int_ch = null;
        assert sharp != null;
        T result = services.getTermBuilder().func(sharp);

        Function identifier = numbers;

        if (intStr.charAt(0) == '-') {
            minusFlag = true;
            intStr =
                    intStr.substring(1);
        }
        // We have to deal with literals coming both from programs and
        // the logic. The former can have prefixes ("0" for octal,
        // "0x" for hex) and suffixes ("L" for long literal). The latter
        // do not have any of these but can have arbitrary length.

        int_ch = intStr.toCharArray();
        length = int_ch.length;

        for (int i = 0; i < length; i++) {
            result =
                    services.getTermBuilder().func(
                            numberSymbol[int_ch[i] - '0'], result);
        }
        if (minusFlag) {
            result = services.getTermBuilder().func(neglit, result);
        }

        return services.getTermBuilder().func(identifier, result);
    }

}
