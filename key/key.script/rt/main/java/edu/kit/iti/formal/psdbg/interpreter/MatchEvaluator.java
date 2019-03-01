package edu.kit.iti.formal.psdbg.interpreter;

import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.DefaultASTVisitor;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.*;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import edu.kit.iti.formal.psdbg.parser.types.TypeFacade;
import lombok.Getter;
import org.apache.commons.lang.NotImplementedException;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Evaluator specially for Expressions in a case "declaration".
 * Created by sarah on 5/22/17.
 */
public class MatchEvaluator extends DefaultASTVisitor<List<VariableAssignment>> implements ScopeObservable {
    @Getter
    private final GoalNode goal;
    private final VariableAssignment state;
    @Getter
    private MatcherApi matcher;
    @Getter
    private List<Visitor> entryListeners = new ArrayList<>(),
            exitListeners = new ArrayList<>();
    private Evaluator eval;

    public MatchEvaluator(VariableAssignment assignment, GoalNode node, MatcherApi matcher) {
        state = new VariableAssignment(assignment); // unmodifiable version of assignment
        goal = node;
        this.matcher = matcher;
        this.eval = new Evaluator(assignment, node);
    }


    /**
     * Evaluation of an expression.
     *
     * @param truth
     * @return
     */
    public List<VariableAssignment> eval(Expression truth) {

        return (List<VariableAssignment>) truth.accept(this);
    }

    @Override
    public List<VariableAssignment> visit(BinaryExpression e) {
        List<VariableAssignment> left = decideEvaluatorAndEvaluate(e.getLeft());
        List<VariableAssignment> right = decideEvaluatorAndEvaluate(e.getRight());
        Operator op = e.getOperator();
        return evaluateExpression(op, left, right);
    }

    @Override
    public List<VariableAssignment> visit(BooleanLiteral booleanLiteral) {
        return transformTruthValue(Value.from(booleanLiteral));
    }

    /**
     * Decide whether to evaluate using the MatchEvaluator or the standard evaluator depending on the content of the expression
     *
     * @param e
     * @return
     */
    private List<VariableAssignment> decideEvaluatorAndEvaluate(Expression e) {
        List<VariableAssignment> evaluatedExpression;
        if (!e.hasMatchExpression()) {
            Value v = (Value) eval(e);
            evaluatedExpression = transformTruthValue(v);
        } else {
            evaluatedExpression = (List<VariableAssignment>) e.accept(this);
        }
        return evaluatedExpression;
    }

    /**
     * TODO rethink
     *
     * @param op
     * @param v1
     * @param v2
     * @return
     */
    private List<VariableAssignment> evaluateExpression(Operator op, List<VariableAssignment> v1, List<VariableAssignment> v2) {
        switch (op) {
            case AND:
                return joinLists(v1, v2);
            case OR:
                return orList(v1, v2);
            case EQ:
                return joinLists(v1, v2);
            case NEQ:
                return null;
            default:
                throw new NotImplementedException("Need to be implemented");
        }
    }

    /**
     * TODO rethink decision: atm. if the first list is true/not empty (but may contain empty assignment) this is returned
     * This decision also results that if a binary expression without a match is printed first, it is the winning assignment
     * Importance of match is decreased with this decision
     *
     * @param v1
     * @param v2
     * @return
     */
    private List<VariableAssignment> orList(List<VariableAssignment> v1, List<VariableAssignment> v2) {
        return (v1.isEmpty()) ? v2 : v1;
    }

    /**
     * If two matching results are conjunctively joined only variable assignments that are compatible with each other can be chosen.
     *
     * @param v1
     * @param v2
     * @return an empty list means false, a list with an assignment means true
     */
    private List<VariableAssignment> joinLists(List<VariableAssignment> v1, List<VariableAssignment> v2) {
        if (v1.isEmpty() || v2.isEmpty()) {
            return v1;
        }
        List<VariableAssignment> compatible = new ArrayList<>();
        for (VariableAssignment variableAssignment1 : v1) {
            List<VariableAssignment> compatibleAssignment = checkForCompatibleAssignment(variableAssignment1, v2);
            if (!compatibleAssignment.isEmpty()) {
                compatible.addAll(compatibleAssignment);
            }
        }
        return compatible;
    }

    private List<VariableAssignment> checkForCompatibleAssignment(VariableAssignment variableAssignment1, List<VariableAssignment> v2) {
        List<VariableAssignment> compatibleAssignments = new ArrayList<>();
        for (VariableAssignment variableAssignment2 : v2) {
            VariableAssignment assignment = variableAssignment1.joinWithCheck(variableAssignment2);
            //check whether an empty assignment was returned, then the join was unsuccessful
            if (!assignment.isEmpty()) {
                compatibleAssignments.add(assignment);
            }

        }
        return compatibleAssignments;
    }


    /**
     * Visit a match expression and decide which matcher to use. currently working is a matcher for sequents and a matcher for labels.
     * @param match
     * @return
     */
    @Override
    public List<VariableAssignment> visit(MatchExpression match) {
        //Signature sig = match.getSignature();
        Value pattern = eval.eval(match.getPattern());
        // Value pattern = (Value) match.getPattern().accept(this);

        List<VariableAssignment> va = null;
        if (pattern.getType() == SimpleType.STRING) {
            va = getMatcher().matchLabel(goal, (String) pattern.getData());
            //TODO extract the results form the matcher in order to retrieve the selection results
        } else if (TypeFacade.isTerm(pattern.getType())) {
            va = getMatcher().matchSeq(goal, (String) pattern.getData());
           // System.out.println("va = " + va);
        }
        return va != null ? va : Collections.emptyList();
    }

    @Override
    public List<VariableAssignment> visit(Variable variable) {
        //get variable value
        Value v = state.getValue(variable);
        if (v != null) {
            // return v;
            return null;
        } else {
            throw new RuntimeException("Variable " + variable + " was not initialized");
        }

    }


    @Override
    public List<VariableAssignment> visit(UnaryExpression e) {
        Operator op = e.getOperator();
        Expression expr = e.getExpression();
        Value exValue = (Value) expr.accept(this);
        Value ret = op.evaluate(exValue);
        return null;
    }


    // public List<VariableAssignment> getMatchedVariables() {
    //     return null;
    // }

    /**
     * Transforms a truth value to its representation as list:
     * If the value is true this method returns a list with an empty assignment
     * If the value is false this method returns an empty list
     *
     * @param v
     * @return
     */
    public List<VariableAssignment> transformTruthValue(Value v) {

        if (v.getType().equals(SimpleType.BOOL)) {
            List<VariableAssignment> transformedValue = new ArrayList<>();
            if (((Boolean) v.getData()).booleanValue() == ((Boolean) Value.TRUE.getData()).booleanValue() || v.getData().equals(Value.TRUE)) {
                transformedValue.add(new VariableAssignment(null));
            }
            return transformedValue;
        } else {
            throw new RuntimeException("This type " + v.getType() + " can not be transformed into a truth value");
        }

    }
}
