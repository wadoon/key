package de.uka.ilkd.key.ldt;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.List;

public class Rational {

    // effectively final, although potentially overwritten in #normalize()
    private BigInteger numerator;

    private BigInteger denominator;

    //@ invariant sign == 0 ==> mantisse.

    public Rational(long value) {
        this(BigInteger.valueOf(value));
    }

    public Rational() {
        this(0l);
    }

    public Rational(BigInteger value) {
        this(value, BigInteger.ONE);
    }

    public Rational(BigInteger numerator, BigInteger denominator) {

        this.numerator = numerator;
        this.denominator = denominator;
        normalize();
    }

    public Rational(double d) {
        this(BigDecimal.valueOf(d));
    }

    public Rational(BigDecimal value) {
        this.numerator = value.unscaledValue();
        this.denominator = BigInteger.TEN.pow(value.scale());
        normalize();
    }

    public Rational(long numerator, long denominator) {
        this(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator));
    }

    public Rational(String value) {
        this(makeBigDecimal(value));
        normalize();
    }

    private static BigDecimal makeBigDecimal(String value) {
        if (value.endsWith("r") || value.endsWith("R")) {
            return new BigDecimal(value.substring(0, value.length() - 1));
        } else {
            throw new NumberFormatException(value);
        }
    }

    private void normalize() {
        if (denominator.equals(BigInteger.ZERO)) {
            throw new ArithmeticException("Rational number: Division by 0");
        }
        if (numerator.equals(BigInteger.ZERO)) {
            denominator = BigInteger.ONE;
        }
        if (denominator.compareTo(BigInteger.ZERO) < 0) {
            numerator = numerator.negate();
            denominator = denominator.negate();
        }

        BigInteger gcd = numerator.gcd(denominator);
        if (!gcd.equals(BigInteger.ONE)) {
            denominator = denominator.divide(gcd);
            numerator = numerator.divide(gcd);
        }
    }


    public BigInteger getNumerator() {
        return numerator;
    }

    public BigInteger getDenominator() {
        return denominator;
    }

    public String toDecimalString() {

        BigInteger[] r = numerator.divideAndRemainder(denominator);
        BigInteger div1 = r[0];
        BigInteger rem = r[1];

        if (rem.equals(BigInteger.ZERO)) {
            return div1.toString() + "r";
        }

        List<BigInteger> remainders = new ArrayList<>();
        StringBuilder digits = new StringBuilder();

        while (!rem.equals(BigInteger.ZERO)) {
            rem = rem.multiply(BigInteger.TEN);
            r = rem.divideAndRemainder(denominator);
            digits.append(r[0].intValue());
            rem = r[1];
            int idx = remainders.indexOf(rem);
            if (idx >= 0) {
                return div1 + "." + digits.substring(0, idx+1) + "(" + digits.substring(idx+1) + ")r";
            }
            remainders.add(rem);
        }

        return div1 + "." + digits + "r";
    }

    public String toFractionString() {
        return numerator + "/" + denominator + "r";
    }
}
