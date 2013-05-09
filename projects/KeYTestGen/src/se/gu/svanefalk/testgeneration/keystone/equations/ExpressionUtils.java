package se.gu.svanefalk.testgeneration.keystone.equations;

import java.util.Map;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.GreaterOrEquals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.LessOrEquals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.AbstractBinaryExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Addition;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Division;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Multiplication;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Negation;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Number;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Subtraction;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;

public class ExpressionUtils {

    private static String dummyVariablePrefix = "keystone_dummyvariable";

    private static int dummyVariableIndex = 1;

    private static ExpressionUtils instance = null;

    public static ExpressionUtils getInstance() {

        if (ExpressionUtils.instance == null) {
            ExpressionUtils.instance = new ExpressionUtils();
        }
        return ExpressionUtils.instance;
    }

    private ExpressionUtils() {

    }

    public IComparator constructExpression(final Term term,
            final Map<String, Variable> variableContext)
            throws KeYStoneException {

        final IExpression leftChild = processTerm(term.sub(0), variableContext);
        final IExpression rightChild = processTerm(term.sub(1), variableContext);

        if (TermParserTools.isEquals(term)) {
            return new Equals(leftChild, rightChild);
        } else if (TermParserTools.isGreaterOrEquals(term)) {
            return new GreaterOrEquals(leftChild, rightChild);
        } else if (TermParserTools.isLessOrEquals(term)) {
            return new LessOrEquals(leftChild, rightChild);
        }

        throw new KeYStoneException("Illegal comparator: " + term);
    }

    private IExpression processBinaryFunction(final Term term,
            final Map<String, Variable> variableContext)
            throws KeYStoneException {

        final IExpression leftChild = processTerm(term.sub(0), variableContext);
        final IExpression rightChild = processTerm(term.sub(1), variableContext);

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

    private IExpression processFunction(final Term term,
            final Map<String, Variable> variableContext)
            throws KeYStoneException {

        if (TermParserTools.isBinaryFunction(term)) {
            return processBinaryFunction(term, variableContext);
        }

        if (TermParserTools.isUnaryFunction(term)) {
            return processUnaryFunction(term, variableContext);
        }

        throw new KeYStoneException("Unsupported Function: " + term.op().name());
    }

    private IExpression processTerm(final Term term,
            final Map<String, Variable> variableContext)
            throws KeYStoneException {

        if (TermParserTools.isFunction(term)) {
            return processFunction(term, variableContext);
        }

        if (TermParserTools.isProgramVariable(term)) {
            return processVariable(term, variableContext);
        }

        if (TermParserTools.isLogicVariable(term)) {
            return processVariable(term, variableContext);
        }

        throw new KeYStoneException("Illegal term: " + term);
    }

    private IExpression processUnaryFunction(final Term term,
            final Map<String, Variable> variableContext)
            throws KeYStoneException {

        if (TermParserTools.isInteger(term)) {
            if (TermParserTools.isIntegerNegation(term.sub(0))) {
                final int value = Integer.parseInt("-"
                        + resolveNumber(term.sub(0).sub(0)));
                return new Negation(new Number(new Fraction(value)));
            } else {
                final int value = Integer.parseInt(resolveNumber(term.sub(0)));
                return new Number(new Fraction(value));
            }
        }
        throw new KeYStoneException("Illegal unary function: " + term);
    }

    private IExpression processVariable(final Term term,
            final Map<String, Variable> variableContext) {

        final String identifier = term.toString();
        return variableContext.get(identifier);
    }

    private String resolveNumber(final Term term) {

        final String numberString = term.op().name().toString();

        if (numberString.equals("#")) {
            return "";
        } else {
            return resolveNumber(term.sub(0)) + numberString;
        }
    }

    public Equals createEqualityFromInequality(IComparator comparator,
            Map<String, Variable> variableIndex, Variable dummyVariable) {

        /*
         * Add slack variable.
         */
        if (comparator instanceof LessOrEquals) {

            IExpression leftOperand = ((LessOrEquals) comparator).getLeftOperand();
            IExpression rightOperand = ((LessOrEquals) comparator).getRightOperand();

            Addition slackAddition = new Addition(leftOperand, dummyVariable);

            variableIndex.put(dummyVariable.getName(), dummyVariable);

            return new Equals(slackAddition, rightOperand);
        }

        /*
         * Add surplus variable.
         */
        if (comparator instanceof GreaterOrEquals) {

            IExpression leftOperand = ((GreaterOrEquals) comparator).getLeftOperand();
            IExpression rightOperand = ((GreaterOrEquals) comparator).getRightOperand();

            variableIndex.put(dummyVariable.getName(), dummyVariable);

            Subtraction surplusSubtraction = new Subtraction(leftOperand,
                    dummyVariable);

            return new Equals(surplusSubtraction, rightOperand);
        }

        return (Equals) comparator;
    }

    public static Variable createDummyVariable() {
        return new Variable(dummyVariablePrefix + dummyVariableIndex++);
    }
}