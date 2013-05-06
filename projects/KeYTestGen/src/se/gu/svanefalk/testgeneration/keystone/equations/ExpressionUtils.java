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
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Number;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Subtraction;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;

public class ExpressionUtils {

    private static int extraVariableIndex = 1;

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

        int x;

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

        if (TermParserTools.isIntegerNegation(term)) {
            final int value = Integer.parseInt("-" + resolveNumber(term.sub(0)));
            return new Number(new Fraction(value));
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

    public Equals removeInequality(IComparator comparator,
            Map<String, Variable> variableIndex) {

        /*
         * Add slack variable.
         */
        if (comparator instanceof LessOrEquals) {

            String variableName = "s" + extraVariableIndex++;
            Variable slackVariable = new Variable(variableName);
            Addition slackAddition = new Addition(
                    ((LessOrEquals) comparator).getLeftOperand(), slackVariable);

            variableIndex.put(variableName, slackVariable);

            return new Equals(slackAddition,
                    ((LessOrEquals) comparator).getRightOperand());
        }

        /*
         * Add surplus variable.
         */
        if (comparator instanceof GreaterOrEquals) {

            String variableName = "s" + extraVariableIndex++;
            Variable surplusVariable = new Variable(variableName);

            variableIndex.put(variableName, surplusVariable);

            Subtraction surplusSubtraction = new Subtraction(
                    ((GreaterOrEquals) comparator).getLeftOperand(),
                    surplusVariable);

            return new Equals(surplusSubtraction,
                    ((GreaterOrEquals) comparator).getRightOperand());
        }

        return (Equals) comparator;
    }
}