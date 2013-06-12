package se.gu.svanefalk.testgeneration.keystone.equations;

import java.util.Map;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.GreaterOrEquals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.LessOrEquals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Addition;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Division;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Multiplication;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.NumericConstant;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Subtraction;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;

public class ExpressionUtils {

    private static ExpressionUtils instance = null;

    public static ExpressionUtils getInstance() {

        if (ExpressionUtils.instance == null) {
            ExpressionUtils.instance = new ExpressionUtils();
        }
        return ExpressionUtils.instance;
    }

    private ExpressionUtils() {

    }

    public IComparator constructRelation(final Term term)
            throws KeYStoneException {

        assert (term != null);

        final IExpression leftChild = processTerm(term.sub(0));
        assert (leftChild != null);

        final IExpression rightChild = processTerm(term.sub(1));
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

            final IExpression leftOperand = ((GreaterOrEquals) comparator).getLeftOperand();
            final IExpression rightOperand = ((GreaterOrEquals) comparator).getRightOperand();

            variableIndex.put(dummyVariable.getName(), dummyVariable);

            final Subtraction surplusSubtraction = new Subtraction(leftOperand,
                    dummyVariable);

            return new Equals(surplusSubtraction, rightOperand);
        }

        return (Equals) comparator;
    }

    private IExpression processBinaryFunction(final Term term)
            throws KeYStoneException {

        final IExpression leftChild = processTerm(term.sub(0));
        final IExpression rightChild = processTerm(term.sub(1));

        if (TermParserTools.isAddition(term)) {
            return new Addition(leftChild, rightChild);
        }

        if (TermParserTools.isSubtraction(term)) {
            return new Subtraction(leftChild, rightChild);
        }

        if (TermParserTools.isMultiplication(term)) {
            return new Multiplication(leftChild, rightChild);
        }

        if (TermParserTools.isDivision(term)) {
            return new Division(leftChild, rightChild);
        }

        throw new KeYStoneException("Illegal binary function: " + term);
    }

    private IExpression processFunction(final Term term)
            throws KeYStoneException {

        if (TermParserTools.isBinaryFunction(term)) {
            return processBinaryFunction(term);
        }

        if (TermParserTools.isUnaryFunction(term)) {
            return processUnaryFunction(term);
        }

        throw new KeYStoneException("Unsupported Function: " + term.op().name());
    }

    private IExpression processTerm(final Term term) throws KeYStoneException {

        if (TermParserTools.isFunction(term)) {
            return processFunction(term);
        }

        if (TermParserTools.isProgramVariable(term)) {
            return processVariable(term);
        }

        if (TermParserTools.isLogicVariable(term)) {
            return processVariable(term);
        }

        throw new KeYStoneException("Illegal term: " + term);
    }

    private IExpression processUnaryFunction(final Term term)
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

    private IExpression processVariable(final Term term) {

        return new Variable(term.toString());
    }
}