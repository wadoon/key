package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import java.util.LinkedList;
import java.util.List;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.restriction.IRestriction;

public class Variable implements IExpression {

    /**
     * Restrictions to be enforced on this variable.
     */
    private final List<IRestriction> restrictions = new LinkedList<>();

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

    public void bind(IExpression expression) {
        this.binding = expression;
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

    public void imposeRestriction(IRestriction restriction) {
        restrictions.add(restriction);
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