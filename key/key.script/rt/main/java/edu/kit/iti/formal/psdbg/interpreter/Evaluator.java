package edu.kit.iti.formal.psdbg.interpreter;

import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.DefaultASTVisitor;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.*;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import edu.kit.iti.formal.psdbg.parser.types.TermType;
import edu.kit.iti.formal.psdbg.parser.types.TypeFacade;
import lombok.Getter;
import lombok.Setter;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Class handling evaluation of expressions (visitor for expressions)
 *
 * @author S.Grebing
 * @author A. Weigl
 */
public class Evaluator<T> extends DefaultASTVisitor<Value> implements ScopeObservable {
    @Getter
    private final VariableAssignment state;
    @Getter
    private final GoalNode<T> goal;
    @Getter
    @Setter
    private MatcherApi<T> matcher;
    @Getter
    private List<Visitor> entryListeners = new ArrayList<>(),
            exitListeners = new ArrayList<>();

    @Getter @Setter
    private Function<TermLiteral, Value> termValueFactory = (TermLiteral l) -> Value.from(l);

    public Evaluator(VariableAssignment assignment, GoalNode<T> node) {
        state = new VariableAssignment(assignment); // unmodifiable version of assignment
        goal = node;
    }

    /**
     * Evaluation of an expression.
     *
     * @param truth
     * @return
     */
    public Value eval(Expression truth) {
        return (Value) truth.accept(this);
    }

    @Override
    public Value visit(BinaryExpression e) {
        Value v1 = (Value) e.getLeft().accept(this);
        Value v2 = (Value) e.getRight().accept(this);
        Operator op = e.getOperator();
        return op.evaluate(v1, v2);
    }

    /**
     * Visit a match expression and evaluate expression using matcher
     *
     * @param match
     * @return
     */
    @Override
    public Value visit(MatchExpression match) {
        enterScope(match);
        List<VariableAssignment> va = null;
        Value pattern = (Value) match.getPattern().accept(this);
        if (match.isDerivable()) {
        } else {
            if (pattern.getType() == SimpleType.STRING) {
                va = matcher.matchLabel(goal, (String) pattern.getData());
            } else if (TypeFacade.isTerm(pattern.getType())) {
                va = matcher.matchSeq(goal, (String) pattern.getData());
            }
        }

        exitScope(match);
        return va != null && va.size() > 0 ? Value.TRUE : Value.FALSE;
    }

    /**
     * TODO Connect with KeY
     * TODO remove return
     *
     * @param term
     * @return
     */
    @Override
    public Value visit(TermLiteral term) {
        return termValueFactory.apply(term);
    }

    @Override
    public Value visit(StringLiteral string) {
        return Value.from(string);
    }

    @Override
    public Value visit(Variable variable) {
        //get variable value
        Value v = state.getValue(variable);
        if (v != null) {
            return v;
        } else {
            throw new RuntimeException("Variable " + variable + " was not initialized");
        }

    }

    @Override
    public Value visit(BooleanLiteral bool) {
        return bool.isValue() ? Value.TRUE : Value.FALSE;
    }


    @Override
    public Value visit(IntegerLiteral integer) {
        return Value.from(integer);
    }

    @Override
    public Value visit(UnaryExpression e) {
        Operator op = e.getOperator();
        Expression expr = e.getExpression();
        Value exValue = (Value) expr.accept(this);
        return op.evaluate(exValue);
    }

    public Value visit(SubstituteExpression expr) {
        Value term = (Value) expr.getSub().accept(this);
        if (term.getType() instanceof TermType) {
            Pattern pattern = Pattern.compile("\\?[a-zA-Z_]+");
            String termstr = term.getData().toString();
            Matcher m = pattern.matcher(termstr);
            StringBuffer newTerm = new StringBuffer();
            while (m.find()) {
                String name = m.group().substring(1); // remove trailing '?'
                Expression t = expr.getSubstitution().get(m.group());

                //either evalute the substituent or find ?X in the
                String newVal = "";
                if (t != null)
                    newVal = ((Value) t.accept(this)).getData().toString();
                else
                    newVal = state.getValue(new Variable(name)).getData().toString();
                m.appendReplacement(newTerm, newVal);
            }
            m.appendTail(newTerm);
            return new Value<>(TypeFacade.ANY_TERM, newTerm.toString());
        } else {
            throw new IllegalStateException("Try to apply substitute on a non-term value.");
        }
    }

    @Override
    public Value visit(FunctionCall func) {
        return func.getFunction().eval(this, func);
    }
}
