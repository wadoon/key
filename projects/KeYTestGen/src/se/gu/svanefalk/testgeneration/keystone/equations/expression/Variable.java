package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Variable extends AbstractExpression {

    /**
     * The expression bound to this variable. Can only be bound once.
     */
    private IExpression binding = null;

    private final String name;

    public Variable(final String name) {
        super();
        this.name = name;
    }

    public void bind(final IExpression expression) {
        binding = expression;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Variable other = (Variable) obj;
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        return true;
    }

    @Override
    public Fraction evaluate() {
        return binding.evaluate();
    }

    /**
     * @return the name
     */
    public String getName() {
        return name;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = (prime * result) + ((name == null) ? 0 : name.hashCode());
        return result;
    }

    public Fraction resolveMultiplier() {

        final ITreeNode parent = getParent();

        /*
         * Find the multiplier.
         */
        Fraction multiplier = null;
        if (parent instanceof Multiplication) {

            final Multiplication parentExpression = (Multiplication) parent;

            if (parentExpression.getLeftOperand() == this) {
                multiplier = parentExpression.getRightOperand().evaluate();
            } else {
                multiplier = parentExpression.getLeftOperand().evaluate();
            }

            /*
             * Determine the sign of the multiplier. There are two cases:
             * 
             * 1) the parent of the multiplication is a negation, in which case
             * the multiplier is also negated.
             * 
             * 2) the parent of the multiplication is a subtraction. Here, the
             * multiplier is negative if our multiplication is the rhand value
             * of such a subtraction, and positive otherwise.
             */
            final ITreeNode parentOfParent = parent.getParent();
            if (parentOfParent instanceof Negation) {
                multiplier = multiplier.multiply(-1);
            } else if (parentOfParent instanceof Subtraction) {

                final Subtraction parentOfParentExpression = (Subtraction) parentOfParent;

                if (parentOfParentExpression.getRightOperand() == parent) {
                    multiplier = multiplier.multiply(-1);
                }
            }
        }

        /*
         * If no multiplier exists, default to 1.
         */
        else {
            multiplier = Fraction.ONE;

            /*
             * Perform the same sign-checking as above.
             */
            if (parent instanceof Negation) {
                multiplier = multiplier.multiply(-1);
            } else if (parent instanceof Subtraction) {

                final Subtraction parentExpression = (Subtraction) parent;

                if (parentExpression.getRightOperand() == this) {
                    multiplier = multiplier.multiply(-1);
                }
            }
        }
        return multiplier;
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