package se.gu.svanefalk.keystone.equations;

import java.util.Map;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.IComparator;
import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;
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

public class ExpressionBuilder {

    private static ExpressionBuilder instance = null;

    private ExpressionBuilder() {

    }

    public static ExpressionBuilder getInstance() {

        if (instance == null) {
            instance = new ExpressionBuilder();
        }
        return instance;
    }

    public IComparator constructExpression(Term term,
            Map<String, Variable> variableContext) throws KeYStoneException {

        IExpression leftChild = processTerm(term.sub(0), variableContext);
        IExpression rightChild = processTerm(term.sub(1), variableContext);

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
            Map<String, Variable> variableContext) throws KeYStoneException {

        IExpression leftChild = processTerm(term.sub(0), variableContext);
        IExpression rightChild = processTerm(term.sub(1), variableContext);

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
            Map<String, Variable> variableContext) throws KeYStoneException {

        if (TermParserTools.isBinaryFunction(term)) {
            return this.processBinaryFunction(term, variableContext);
        }

        if (TermParserTools.isUnaryFunction(term)) {
            return this.processUnaryFunction(term, variableContext);
        }

        throw new KeYStoneException("Unsupported Function: " + term.op().name());
    }

    private IExpression processTerm(final Term term,
            Map<String, Variable> variableContext) throws KeYStoneException {

        if (TermParserTools.isFunction(term)) {
            return this.processFunction(term, variableContext);
        }

        if (TermParserTools.isProgramVariable(term)) {
            return this.processVariable(term, variableContext);
        }

        if (TermParserTools.isLogicVariable(term)) {
            return this.processVariable(term, variableContext);
        }

        throw new KeYStoneException("Illegal term: " + term);
    }

    private IExpression processUnaryFunction(final Term term,
            Map<String, Variable> variableContext) throws KeYStoneException {

        if (TermParserTools.isIntegerNegation(term)) {
            final int value = Integer.parseInt("-"
                    + this.resolveNumber(term.sub(0)));
            return new Number(new Fraction(value));
        }
        throw new KeYStoneException("Illegal unary function: " + term);
    }

    private IExpression processVariable(final Term term,
            Map<String, Variable> variableContext) {

        final String identifier = term.toString();
        return variableContext.get(identifier);
    }

    private String resolveNumber(final Term term) {

        final String numberString = term.op().name().toString();

        if (numberString.equals("#")) {
            return "";
        } else {
            return this.resolveNumber(term.sub(0)) + numberString;
        }
    }
}