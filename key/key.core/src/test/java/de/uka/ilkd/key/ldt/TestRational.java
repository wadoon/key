package de.uka.ilkd.key.ldt;

import org.junit.Test;

import java.math.BigInteger;

import static org.junit.Assert.*;

public class TestRational {

    @Test
    public void testToDecimalString() throws Exception {

        assertEquals("50r", new Rational(50.).toDecimalString());
        assertEquals("0.5r", new Rational(.5).toDecimalString());
        assertEquals("1.1(2)r", new Rational(101l,90).toDecimalString());
        assertEquals("0.65(24)r", new Rational(6459l, 9900).toDecimalString());
        assertEquals("0.(3)r", new Rational(1,3));
    }

    @Test
    public void normalization() throws Exception {
        assertEquals("-1/2r", new Rational(-.5).toFractionString());
        assertEquals("-1/2r", new Rational(22, -44).toFractionString());
        assertEquals("1/2r", new Rational(-1, -2).toFractionString());
        assertEquals("-1/2r", new Rational(-1, 2).toFractionString());
        assertEquals("-1/2r", new Rational(new BigInteger("111111111111"), new BigInteger("-222222222222")).toFractionString());
    }
}