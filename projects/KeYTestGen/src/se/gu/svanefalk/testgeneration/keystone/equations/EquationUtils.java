package se.gu.svanefalk.testgeneration.keystone.equations;

import java.util.Map;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.GreaterOrEquals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.LessOrEquals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Addition;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Division;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.ExpressionUtils;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Multiplication;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.NumericConstant;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;

public class EquationUtils {

    private static EquationUtils instance = null;

    public static IComparator constructRelation(final Term term)
            throws KeYStoneException {

        assert (term != null);

        final IExpression leftChild = EquationUtils.processTerm(term.sub(0));
        assert (leftChild != null);

        final IExpression rightChild = EquationUtils.processTerm(term.sub(1));
        assert (rightChild != null);

        if (TermParserTools.isEquals(term)) {
            return new Equals(leftChild, rightChild);
        } else if (TermParserTools.isGreaterOrEquals(term)) {
            return new GreaterOrEquals(leftChild, rightChild);
        } else if (TermParserTools.isLessOrEquals(term)) {
            return new LessOrEquals(leftChild, rightChild);
        }

        throw new KeYStoneException("Illegal comparator: " + term);
    }

    public static EquationUtils getInstance() {

        if (EquationUtils.instance == null) {
            EquationUtils.instance = new EquationUtils();
        }
        return EquationUtils.instance;
    }

    private static IExpression processBinaryFunction(final Term term)
            throws KeYStoneException {

        final IExpression leftChild = EquationUtils.processTerm(term.sub(0));
        final IExpression rightChild = EquationUtils.processTerm(term.sub(1));

        if (TermParserTools.isAddition(term)) {
            final Addition addition = new Addition(leftChild, rightChild);
            return addition;
        }

        /*
         * Subtraction requires case distinction depending on exactly what is
         * being subtracted.
         */
        if (TermParserTools.isSubtraction(term)) {
            final Addition addition = new Addition(leftChild, rightChild);
            ExpressionUtils.negateAddition(addition);
            return addition;
        }

        if (TermParserTools.isDivision(term)) {
            return new Division(leftChild, rightChild);
        }

        if (TermParserTools.isMultiplication(term)) {
            return new Multiplication(leftChild, rightChild);
        }

        throw new KeYStoneException("Illegal binary function: " + term);
    }

    private static IExpression processFunction(final Term term)
            throws KeYStoneException {

        if (TermParserTools.isBinaryFunction(term)) {
            return EquationUtils.processBinaryFunction(term);
        }

        if (TermParserTools.isUnaryFunction(term)) {
            return EquationUtils.processUnaryFunction(term);
        }

        throw new KeYStoneException("Unsupported Function: " + term.op().name());
    }

    private static IExpression processTerm(final Term term)
            throws KeYStoneException {

        if (TermParserTools.isFunction(term)) {
            return EquationUtils.processFunction(term);
        }

        if (TermParserTools.isProgramVariable(term)) {
            return EquationUtils.processVariable(term);
        }

        if (TermParserTools.isLogicVariable(term)) {
            return EquationUtils.processVariable(term);
        }

        throw new KeYStoneException("Illegal term: " + term);
    }

    private static IExpression processUnaryFunction(final Term term)
            throws KeYStoneException {

        if (TermParserTools.isInteger(term)) {
            if (TermParserTools.isIntegerNegation(term.sub(0))) {
                final int value = Integer.parseInt("-"
                        + TermParserTools.resolveNumber(term.sub(0).sub(0)));
                return new NumericConstant(new Fraction(value));
            } else {
                final int value = Integer.parseInt(TermParserTools.resolveNumber(term.sub(0)));
                return new NumericConstant(new Fraction(value));
            }
        }
        throw new KeYStoneException("Illegal unary function: " + term);
    }

    private static IExpression processVariable(final Term term) {

        return new Variable(term.toString());
    }

    private EquationUtils() {

    }

    public Equals createEqualityFromInequality(final IComparator comparator,
            final Map<String, Variable> variableIndex,
            final Variable dummyVariable) {

        /*
         * Add slack variable.
         */
        if (comparator instanceof LessOrEquals) {

            final IExpression leftOperand = ((LessOrEquals) comparator).getLeftOperand();
            final IExpression rightOperand = ((LessOrEquals) comparator).getRightOperand();

            final Addition slackAddition = new Addition(leftOperand,
                    dummyVariable);

            variableIndex.put(dummyVariable.getName(), dummyVariable);

            return new Equals(slackAddition, rightOperand);
        }

        /*
         * Add surplus variable.
         */
        if (comparator instanceof GreaterOrEquals) {

            dummyVariable.negate();

            final IExpression leftOperand = ((GreaterOrEquals) comparator).getLeftOperand();
            final IExpression rightOperand = ((GreaterOrEquals) comparator).getRightOperand();

            variableIndex.put(dummyVariable.getName(), dummyVariable);

            final Addition surplusSubtraction = new Addition(leftOperand,
                    dummyVariable);

            return new Equals(surplusSubtraction, rightOperand);
        }

        return (Equals) comparator;
    }
}
