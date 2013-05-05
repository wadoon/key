package se.gu.svanefalk.keystone.equations.expression;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.keystone.equations.IExpression;

public class Number implements IExpression {

    private Fraction value = null;

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
    public void setValue(Fraction value) {
        this.value = value;
    }
}