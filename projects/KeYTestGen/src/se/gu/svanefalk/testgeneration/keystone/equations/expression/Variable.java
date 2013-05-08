package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Variable implements IExpression {

    /**
     * The expression bound to this variable. Can only be bound once.
     */
    private IExpression binding = null;

    private final String name;

    /**
     * @return the name
     */
    public String getName() {
        return name;
    }

    public Variable(String name) {
        super();
        this.name = name;
    }

    public void bind(IExpression expression)
            throws OperationNotSupportedException {

        if (binding == null) {
            this.binding = expression;
        } else {
            throw new OperationNotSupportedException(
                    "Attempted to bind already bound variable");
        }
    }

    @Override
    public Fraction evaluate() throws OperationNotSupportedException {
        if (binding != null) {
            return binding.evaluate();
        } else {
            throw new OperationNotSupportedException(
                    "Attempted to evaluate unbound variable");
        }
    }

    @Override
    public String toString() {

        if (binding == null) {
            return name;
        } else {
            return binding.toString();
        }
    }
}