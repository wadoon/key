package se.gu.svanefalk.testgeneration.keystone.equations;

import java.util.HashSet;
import java.util.Set;

import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.AbstractBinaryExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;

/**
 * Instances of this class represent equations.
 * 
 * @author christopher
 * 
 */
public class Equation {

    /**
     * The root of the equation itself.
     */
    private final Equals root;

    private final Set<Variable> variables;

    private Equation(Equals root, Set<Variable> variables) {
        super();
        this.root = root;
        this.variables = variables;
    }

    public static Equation createEquation(Equals root) {

        Set<Variable> variables = extractVariables(root);
        return new Equation(root, variables);
    }

    /**
     * Creates a set of all variables in the equation.
     * 
     * @param root
     * @return
     */
    private static Set<Variable> extractVariables(Equals root) {

        Set<Variable> variables = new HashSet<>();

        extractVariables_helper(root.getLeftOperand(), variables);
        extractVariables_helper(root.getRightOperand(), variables);

        return variables;
    }

    /**
     * Helper for {@link #extractVariables(Equals)}.
     * 
     * @param expression
     * @param variables
     */
    private static void extractVariables_helper(IExpression expression,
            Set<Variable> variables) {

        if (expression instanceof Variable) {
            variables.add((Variable) expression);
        } else if (expression instanceof AbstractBinaryExpression) {
            AbstractBinaryExpression abstractExpression = (AbstractBinaryExpression) expression;
            extractVariables_helper(abstractExpression.getLeftOperand(),
                    variables);
            extractVariables_helper(abstractExpression.getRightOperand(),
                    variables);
        }
    }

    /**
     * Solves this equation in order to get a binding for the target variable.
     * Please note that this permanently changes the structure of the equation
     * (albeit not the semantics).
     * 
     * @param variables
     */
    private void solveForVariable(Variable variables) {

        /*
         * Isolate the variable to one side of the equation.
         */

    }
}