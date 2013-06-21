package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import org.apache.commons.math3.fraction.Fraction;

public class NumericConstant extends AbstractExpression {

    private Fraction value = null;

    public NumericConstant(final Fraction fraction) {
        value = fraction;
    }

    public NumericConstant(final int value) {
        this(new Fraction(value));
    }

    @Override
    public Fraction evaluate() {
        return getValue();
    }

    /**
     * @return the value
     */
    public Fraction getValue() {
        return value;
    }

    /**
     * @param value
     *            the value to set
     */
    public void setValue(final Fraction value) {
        this.value = value;
    }

    @Override
    public String toString() {

        return value.toString();
    }
}