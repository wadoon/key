package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Number implements IExpression {

    private Fraction value = null;

    public Number(final Fraction fraction) {
        value = fraction;
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
}