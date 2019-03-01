package edu.kit.iti.formal.psdbg.interpreter;


import edu.kit.iti.formal.psdbg.interpreter.assignhook.VariableAssignmentHook;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.InterpreterRuntimeException;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.CommandLookup;
import edu.kit.iti.formal.psdbg.parser.DefaultASTVisitor;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.*;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import lombok.Getter;
import lombok.Setter;
import org.antlr.v4.runtime.ParserRuleContext;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Main Class for interpreter
 * Interpreter keeps a stack of states
 *
 * @author S.Grebing
 */
public class Interpreter<T> extends DefaultASTVisitor<Object>
        implements ScopeObservable {
    protected static Logger logger = LogManager.getLogger(Interpreter.class);

    @Getter
    public final AtomicBoolean hardStop = new AtomicBoolean(false);
    @Getter
    private final List<VariableAssignmentHook<T>> variableHooks = new LinkedList<>();
    @Getter
    protected List<Visitor> entryListeners = new ArrayList<>(),
            exitListeners = new ArrayList<>();
    /**
     *
     */
    @Getter
    @Setter
    private int maxIterationsRepeat = 10000;
    private Stack<State<T>> stateStack = new Stack<>();
    @Getter
    @Setter
    private MatcherApi<T> matcherApi;
    @Getter
    private CommandLookup functionLookup;
    @Getter
    @Setter
    private boolean strictMode = false;
    @Getter
    @Setter
    private boolean suppressListeners = false;

    public Interpreter(CommandLookup lookup) {
        functionLookup = lookup;
    }

    @Override
    public <T extends ParserRuleContext> void enterScope(ASTNode<T> node) {
        if (hardStop.get())
            throw new InterpreterRuntimeException("hard stop");
        if (!suppressListeners) callListeners(getEntryListeners(), node);
    }

    @Override
    public <T extends ParserRuleContext> void exitScope(ASTNode<T> node) {
        if (!suppressListeners) callListeners(getExitListeners(), node);
    }

    /**
     * starting point is a statement list
     */
    public void interpret(ProofScript script) {
        //enterScope(script);
        if (stateStack.empty()) {
            throw new InterpreterRuntimeException("no state on stack. call newState before interpret");
        }

        if (getSelectedNode() != null) {
            //initialize environment variables
            for (VariableAssignmentHook<T> hook : variableHooks) {
                VariableAssignment va = hook.getStartAssignment(getSelectedNode().getData());
                getSelectedNode().setAssignments(
                        getSelectedNode().getAssignments().push(va));
            }
        } else {
            List<GoalNode<T>> currentgoals = getCurrentGoals();
            logger.info("Loaded Proof with multiple Open Goals");
            if (currentgoals.size() == 0) {
                logger.debug("Current Goals empty");
                return;
            }

            for (GoalNode<T> goal : currentgoals) {
                for (VariableAssignmentHook<T> hook : variableHooks) {
                    VariableAssignment va = hook.getStartAssignment(goal.getData());
                    goal.setAssignments(
                            goal.getAssignments().push(va));
                }
            }

        }
        script.accept(this);
        //exitScope(script);
    }

    /**
     * Visit a proof script (context is handled by the call of the script noch by visiting the script itself)
     * 1) visit its signature
     * 2) visit its body
     *
     * @param proofScript
     * @return
     */
    @Override
    public Object visit(ProofScript proofScript) {
        //add vars
        visit(proofScript.getSignature());
        //weigl: disabled because it is strange enterScope(proofScript);
        proofScript.getBody().accept(this);
        //exitScope(proofScript);
        return null;
    }

    /**
     * Visiting an assignment results in changing the variables of the current selected goalnode
     *
     * @param assignmentStatement
     * @return
     */
    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        enterScope(assignmentStatement);

        GoalNode<T> node = getSelectedNode();
        Type t = assignmentStatement.getType();
        Variable var = assignmentStatement.getLhs();
        Expression expr = assignmentStatement.getRhs();
        if (t != null) {
            node.declareVariable(var, t);
        }

        if (expr != null) {
            Type type = node.getVariableType(var);
            if (type == null) {
                throw new RuntimeException("SimpleType of Variable " + var + " is not declared yet");
            } else {
                Value v = evaluate(expr);
                if (fireVariableAssignmentHook(node, var.getIdentifier(), v)) {
                    node.setVariableValue(var, v);
                }
                node.setVariableValue(var, v);
            }
        }
        exitScope(assignmentStatement);

        return null;
    }

    protected boolean fireVariableAssignmentHook(GoalNode<T> node, String identifier, Value v) {
        for (VariableAssignmentHook<T> hook : variableHooks) {
            if (hook.handleAssignment(node.getData(), identifier, v)) {
                return true;
            }
        }
        return variableHooks.size() == 0;
    }

    protected Value evaluate(Expression expr) {
        return evaluate(getSelectedNode(), expr);
    }

    private Value evaluate(GoalNode<T> g, Expression expr) {
        //enterScope(expr);
        Evaluator<T> evaluator = createEvaluator(g.getAssignments(), g);
        //exitScope(expr);
        return evaluator.eval(expr);
    }

    protected Evaluator<T> createEvaluator(VariableAssignment assignments, GoalNode<T> g) {
        Evaluator<T> evaluator = new Evaluator<>(assignments, g);
        evaluator.setMatcher(matcherApi);
        return evaluator;
    }


    /**
     * Visiting a statement list results in visiting each statement
     *
     * @param statements
     * @return
     */
    @Override
    public Void visit(Statements statements) {
        enterScope(statements);
        for (Statement s : statements) {
            s.accept(this);
        }
        exitScope(statements);
        return null;
    }

    /**
     * @param casesStatement
     * @return
     */
    @Override
    public Object visit(CasesStatement casesStatement) {
        enterScope(casesStatement);
        State<T> beforeCases = peekState();

        List<GoalNode<T>> allGoalsBeforeCases = beforeCases.getGoals();
        //copy the list of goal nodes for keeping track of goals
        Set<GoalNode<T>> toMatch = new HashSet<>(allGoalsBeforeCases);

        //global List after all Case Statements
        List<GoalNode<T>> resultingGoals = new ArrayList<>();

        //handle cases
        List<CaseStatement> cases = casesStatement.getCases();

        for (GoalNode<T> goal : allGoalsBeforeCases) {
            newState(goal); //to allow the visit method for the case statement to retrieve goal

            boolean result = false;
            for (CaseStatement aCase : cases) {
                result = (boolean) aCase.accept(this);
                if (result) {
                    //remove goal from set for default
                    toMatch.remove(goal);
                    //case statement matched and was executed
                    break;
                }
            }

            State<T> stateAfterCase = popState(); //remove state from stack
            if (stateAfterCase.getSelectedGoalNode() != null) {
                assert stateAfterCase.getGoals().contains(stateAfterCase.getSelectedGoalNode());
            }

            if (result && stateAfterCase.getGoals() != null) {
                resultingGoals.addAll(stateAfterCase.getGoals());
            }
        }


        //for all remaining goals execute default case
        //we need an entry/exit listener for default case
        if (!toMatch.isEmpty()) {
            VariableAssignment va = new VariableAssignment();
            //Statements defaultCase = casesStatement.getDefaultCase();
            DefaultCaseStatement defCaseStmt = casesStatement.getDefCaseStmt();
            for (GoalNode<T> goal : toMatch) {
                resultingGoals.addAll(executeDefaultCase(defCaseStmt, goal, va).getGoals());
                // resultingGoals.addAll(executeBody(defaultCase, goal, va).getGoals());
            }
        }

        //exit scope and create a new state using the union of all newly created goals

        State<T> newStateAfterCases;
        if (!resultingGoals.isEmpty()) {
            //goalsAfterCases.forEach(node -> node.exitScope());
            Stream<GoalNode<T>> goalNodeStream = resultingGoals.stream().filter(tGoalNode -> !(tGoalNode.isClosed()));
            List<GoalNode<T>> openGoalListAfterCases = goalNodeStream.collect(Collectors.toList());

            if (openGoalListAfterCases.size() == 1) {
                newStateAfterCases = new State<T>(openGoalListAfterCases, 0);
            } else {
                newStateAfterCases = new State<T>(openGoalListAfterCases, null);
            }
            stateStack.push(newStateAfterCases);

        } else {
            stateStack.push(new State<>());
        }

        //stateStack.peek().getGoals().removeAll(beforeCases.getGoals());
        exitScope(casesStatement);
        return null;
    }

    private State<T> executeDefaultCase(DefaultCaseStatement defCaseStmt, GoalNode<T> goal, VariableAssignment va) {
        enterScope(defCaseStmt);
        State<T> newState = executeBody(defCaseStmt.getBody(), goal, va);
        exitScope(defCaseStmt);
        return newState;
    }

    @Override
    public Object visit(GuardedCaseStatement guardedCaseStatement) {
        Expression matchExpression = guardedCaseStatement.getGuard();
        State<T> currentStateToMatch = peekState();
        GoalNode<T> selectedGoal = currentStateToMatch.getSelectedGoalNode();
        assert currentStateToMatch.getGoals().contains(selectedGoal);
        VariableAssignment va = evaluateMatchInGoal(matchExpression, selectedGoal);

        try {
            enterScope(guardedCaseStatement);
            if (va != null) {
                executeBody(guardedCaseStatement.getBody(), selectedGoal, va);
                return true;
            } else {
                return false;
            }
        } finally {
            exitScope(guardedCaseStatement);
        }
    }

    /**
     * Computes which goals are handled by the different cases in the order the cases appear in the script
     * @param allGoalsBeforeCases
     * @param cases all cases as ordered list
     * @return a mapping of each goal to the matched case body together with variableassignments from the matching process
     */
  /*  private Map<GoalNode, Pair<VariableAssignment, Statements>> matchGoalsToCases(List<GoalNode<T>> allGoalsBeforeCases, CasesStatement cases) {
        //list of cases
        List<CaseStatement> caseStmts = cases.getCases();
        //remaining goals
        Set<GoalNode<T>> setOfRemainingGoals = Sets.newHashSet(allGoalsBeforeCases);

        //returnMap
        Map<GoalNode, Pair<VariableAssignment, Statements>> returnMap = new HashMap<>();

        for (CaseStatement caseStmt : caseStmts) {
            Map<GoalNode<T>, VariableAssignment> goalNodeVariableAssignmentMap = matchGoal(setOfRemainingGoals, caseStmt);
            //put all matched goals to returnMap for case
            goalNodeVariableAssignmentMap.keySet().forEach(tGoalNode ->
            {
                returnMap.put(tGoalNode, new Pair<VariableAssignment, Statements>(goalNodeVariableAssignmentMap.get(tGoalNode), caseStmt.getBody()));
            });
            setOfRemainingGoals.removeAll(goalNodeVariableAssignmentMap.keySet());
        }

        if (!setOfRemainingGoals.isEmpty()) {
            VariableAssignment va = new VariableAssignment();
            Statements defaultCase = cases.getDefaultCase();
            for (GoalNode<T> goal : setOfRemainingGoals) {
                returnMap.put(goal, new Pair<VariableAssignment, Statements>(va, defaultCase));
                // resultingGoals.addAll(executeBody(defaultCase, goal, va).getGoals());
            }
        }
        return returnMap;


    }*/

    /**
     * Match a set of goal nodes against a matchpattern of a case and return the matched goals together with instantiated variables
     */
  /*  private Map<GoalNode<T>, VariableAssignment> matchGoal(Set<GoalNode<T>> allGoalsBeforeCases, CaseStatement aCase) {

        HashMap<GoalNode<T>, VariableAssignment> matchedGoals = new HashMap<>();
        if (!aCase.isClosedStmt()) {
            GuardedCaseStatement caseStmt = (GuardedCaseStatement) aCase;
            Expression matchExpression = caseStmt.getGuard();
            for (GoalNode<T> goal : allGoalsBeforeCases) {
                VariableAssignment va = evaluateMatchInGoal(matchExpression, goal);
                if (va != null) {
                    matchedGoals.put(goal, va);
                }
            }
            return matchedGoals;
        } else {
            //handle try and closes
            if(aCase instanceof ClosesCase){
                ClosesCase closesCase = (ClosesCase) aCase;
                for (GoalNode<T> goal : allGoalsBeforeCases) {
                    //put state onto stack
                    newState(goal);
                    boolean matched = (Boolean) closesCase.accept(this);
                    if (matched) {
                        matchedGoals.put(goal, new VariableAssignment(null));
                    }
                }
                return matchedGoals;
            }else{
                TryCase tryCase = (TryCase) aCase;
                for (GoalNode<T> goal : allGoalsBeforeCases) {
                    //put state onto stack
                    newState(goal);
                    boolean matched = (Boolean) tryCase.accept(this);
                    if (matched) {
                        matchedGoals.put(goal, new VariableAssignment(null));
                    }
                }
                return matchedGoals;

            }


        }
    }*/

/*
    public Object visitOld(CasesStatement casesStatement) {
        enterScope(casesStatement);
        State<T> beforeCases = peekState();

        List<GoalNode<T>> allGoalsBeforeCases = beforeCases.getGoals();
        //copy the list of goal nodes for keeping track of goals
        Set<GoalNode<T>> toMatch = new HashSet<>(allGoalsBeforeCases);

        //global List after all Case Statements
        List<GoalNode<T>> resultingGoals = new ArrayList<>();

        //handle cases
        List<CaseStatement> cases = casesStatement.getCases();

        Map<GoalNode, Pair<VariableAssignment, Statements>> goalToCaseMapping = matchGoalsToCases(allGoalsBeforeCases, casesStatement);

        goalToCaseMapping.forEach((goalNode, variableAssignmentStatementsPair) -> {
            if(variableAssignmentStatementsPair.getValue().isEmpty()){
                //TODO this is the try case
            }else {
                State<T> createdState = newState(goalNode);
                executeBody(variableAssignmentStatementsPair.getValue(), goalNode, variableAssignmentStatementsPair.getKey());
                //stmts.accept(this);

                State<T> stateAfterCase = popState(); //remove state from stack
                if (stateAfterCase.getGoals() != null) {
                    resultingGoals.addAll(stateAfterCase.getGoals());
                }
            }
        });

        //exit scope and create a new state using the union of all newly created goals

        State<T> newStateAfterCases;
        if (!resultingGoals.isEmpty()) {
            //goalsAfterCases.forEach(node -> node.exitScope());
            Stream<GoalNode<T>> goalNodeStream = resultingGoals.stream().filter(tGoalNode -> !(tGoalNode.isClosed()));
            List<GoalNode<T>> openGoalListAfterCases = goalNodeStream.collect(Collectors.toList());

            if (openGoalListAfterCases.size() == 1) {
                newStateAfterCases = new State<T>(openGoalListAfterCases, 0);
            } else {
                newStateAfterCases = new State<T>(openGoalListAfterCases, null);
            }
            stateStack.push(newStateAfterCases);
        }

        //stateStack.peek().getGoals().removeAll(beforeCases.getGoals());
        exitScope(casesStatement);
        return null;
    }*/
   /* @Override
    public Object visit(TryCase TryCase) {
        enterScope(TryCase);
        //is handled by KeYInterpreter
        exitScope(TryCase);
        return false;
    }*/

    /**
     * Evaluate a match in a specific goal
     *
     * @param matchExpression
     * @param goal
     * @return null, if match was false, return the first Assignment when match was true
     */
    private VariableAssignment evaluateMatchInGoal(Expression matchExpression, GoalNode<T> goal) {
        enterScope(matchExpression);
        List<VariableAssignment> matchResult;
        if (matchExpression.hasMatchExpression()) {
            MatchEvaluator mEval = new MatchEvaluator(goal.getAssignments(), goal, matcherApi);
            mEval.getEntryListeners().addAll(getEntryListeners());
            mEval.getExitListeners().addAll(getExitListeners());
            matchResult = mEval.eval(matchExpression);
            exitScope(matchExpression);
        } else {

            matchResult = new ArrayList<>();
            Evaluator eval = new Evaluator(goal.getAssignments(), goal);
            Value eval1 = eval.eval(matchExpression);
            if (eval1.getType().equals(SimpleType.BOOL) && eval1.equals(Value.TRUE)) {
                VariableAssignment emptyAssignment = new VariableAssignment(null);
                matchResult.add(emptyAssignment);
            }
            exitScope(matchExpression);
        }
        if (matchResult.isEmpty()) {
            return null;
        } else {
            return matchResult.get(0);
        }

        /*Evaluator eval = new Evaluator(goal.getAssignments(), goal);
        eval.setMatcher(matcherApi);
        eval.getEntryListeners().addAll(entryListeners);
        eval.getExitListeners().addAll(exitListeners);
        exitScope(matchExpression);

        Value v = eval.eval(matchExpression);
        if (v.getData().equals(Value.TRUE)) {
            if (eval.getMatchedVariables().size() == 0) {
                return new VariableAssignment();
            } else {
                return eval.getMatchedVariables().get(0);
            }
        }
        return null;*/
    }

    /**
     * For each selected goal put a state onto the stack and visit the body of the case
     *
     * @param
     * @param caseStmts
     * @param goalsToApply @return
     */
    private List<GoalNode<T>> executeCase(Statements caseStmts,
                                          Map<GoalNode<T>, VariableAssignment> goalsToApply) {
        enterScope(caseStmts);
        List<GoalNode<T>> goalsAfterCases = new ArrayList<>();

        for (Map.Entry<GoalNode<T>, VariableAssignment> next : goalsToApply.entrySet()) {
            State<T> s = executeBody(caseStmts, next.getKey(), next.getValue());
            goalsAfterCases.addAll(s.getGoals());
        }
        exitScope(caseStmts);
        return goalsAfterCases;


    }

    protected State<T> executeBody(Statements caseStmts, GoalNode<T> goalNode, VariableAssignment va) {
        enterScope(caseStmts);
        goalNode.enterScope(va);
        State<T> s = newState(goalNode);
        assert s.getGoals().contains(s.getSelectedGoalNode());
        caseStmts.accept(this);
        //popState(s); //This may be incorrect-> Bug? -> Cases Statement needs to pop, as goals need to be collected
        exitScope(caseStmts);
        return s;
    }

    /**
     * Visiting a call statement results in:
     * 0) searching for the handler of the called command
     * 1) saving the context onto the stack and creating a copy of the state and push it onto the stack
     * 2) adding new Variable Assignments to te selected goal
     * 3) adding the assigned parameters to the variable assignments
     * 4) visiting the body respec. letting the handler take over
     * 5) removing the top element form the stack
     *
     * @param call
     * @return
     */
    @Override
    public Object visit(CallStatement call) {
        enterScope(call);
        if (!call.getCommand().isEmpty()) //real call, can handle pseudo calls!
        {
            //neuer VarScope
            //enter new variable scope
            VariableAssignment params;
            GoalNode<T> g = null;
            boolean unInterpretedParams = functionLookup.isUninterpretedParams(call);
            if (!unInterpretedParams) {
                params = evaluateParameters(call.getParameters());
                g = getSelectedNode();
                g.enterScope();
            } else {
                params = evaluateParametersStateLess(call.getParameters());

            }
            try {
                functionLookup.callCommand(this, call, params);

            } catch (RuntimeException e) {
                System.err.println("Call command " + call.getCommand() + "not applicable");
                throw e;
                //TODO handling of error state for each visit
                //State<T> newErrorState = newState(null, null);
                //newErrorState.setErrorState(true);
                //pushState(newErrorState);
            } finally {
                if (!unInterpretedParams) {
                    //TODO this may not be needed
                    g.exitScope();
                }
            }

        }
        exitScope(call);
        return null;
    }

    private VariableAssignment evaluateParametersStateLess(Parameters parameters) {
        VariableAssignment va = new VariableAssignment();
        Evaluator<T> evaluator = new Evaluator<>(null, null);

        parameters.entrySet().forEach(entry -> {
            try {
                Value val = evaluate(entry.getValue());
                va.declare(entry.getKey(), val.getType());
                va.assign(entry.getKey(), val);
            } catch (NullPointerException npe) {
                System.out.println("Caught Nullpointer in evaluation of Stateless parameters: " + entry.toString()
                );
                Value val = evaluator.eval(entry.getValue());
                va.declare(entry.getKey(), val.getType());
                va.assign(entry.getKey(), val);
            }
        });
        return va;
    }

    public VariableAssignment evaluateParameters(Parameters parameters) {
        VariableAssignment va = new VariableAssignment();
        parameters.entrySet().forEach(entry -> {
            Value val = evaluate(entry.getValue());
            va.declare(entry.getKey(), val.getType());
            va.assign(entry.getKey(), val);
        });
        return va;
    }

    @Override
    public Object visit(TheOnlyStatement theOnly) {
        List<GoalNode<T>> goals = getCurrentState().getGoals();
        if (goals.size() > 1) {
            throw new IllegalArgumentException(
                    String.format("TheOnly at line %d: There are %d goals!",
                            theOnly.getStartPosition().getLineNumber(),
                            goals.size()));
        }
        enterScope(theOnly);
        theOnly.getBody().accept(this);
        exitScope(theOnly);
        return null;
    }

    /**
     * Visiting foreach:
     * 1) foreach goal in state create a new state with exact this goal
     * 2) foreach of these goals visit body of foreach
     * 3) collect all results after foreach
     *
     * @param foreach
     * @return
     */
    @Override
    public Object visit(ForeachStatement foreach) {
        enterScope(foreach);
        List<GoalNode<T>> allGoals = getCurrentGoals();
        List<GoalNode<T>> goalsAfterForeach = new ArrayList<>();
        Statements body = foreach.getBody();
        for (GoalNode<T> goal : allGoals) {
            newState(goal);
            visit(body);
            State<T> s = popState();
            goalsAfterForeach.addAll(s.getGoals());
        }
        State<T> afterForeach = new State<T>(goalsAfterForeach, null);
        stateStack.push(afterForeach);
        exitScope(foreach);
        return null;
    }

    @Override
    public Object visit(RepeatStatement repeatStatement) {
        enterScope(repeatStatement);
        int counter = 0;
        boolean b = false;
        try {
            do {
                counter++;
                State<T> prev = getCurrentState();
                repeatStatement.getBody().accept(this);
                State<T> end = getCurrentState();

                Set<GoalNode<T>> prevNodes = new HashSet<>(prev.getGoals());
                Set<GoalNode<T>> endNodes = new HashSet<>(end.getGoals());
                b = prevNodes.equals(endNodes);
                b = !b && counter <= maxIterationsRepeat;
            } while (b);
        } catch (InterpreterRuntimeException e) {
            logger.debug("Catched!", e);
        }
        exitScope(repeatStatement);
        return null;
    }

    @Override
    public Object visit(Signature signature) {
        //  enterScope(signature);

        // TODO: quickfix

        List<GoalNode<T>> currentGoals = getCurrentGoals();
        if (getCurrentGoals().size() > 1) {
            if (getSelectedNode() == null) {
                for (GoalNode<T> goal : currentGoals) {

                    goal.enterScope();
                    signature.forEach(goal::declareVariable);
                    // exitScope(signature);

                }
            }
        } else {
            GoalNode<T> node = getSelectedNode();
            node.enterScope();
            signature.forEach(node::declareVariable);
            // exitScope(signature);
        }
        return null;
    }

    //region State Handling
    public GoalNode<T> getSelectedNode() {
        try {
            GoalNode<T> selectedGoalNode = stateStack.peek().getSelectedGoalNode();
            if (selectedGoalNode != null) {
                assert stateStack.peek().getGoals().contains(selectedGoalNode);
                return selectedGoalNode;
            } else {
                throw new IllegalStateException();
            }
        } catch (IllegalStateException e) {
            if (strictMode)
                throw e;

            logger.warn("No goal selected. Returning first goal!");
            return getCurrentGoals().get(0);
        }
    }

    /**
     * Peek current state
     *
     * @return state on top of state stack
     */
    public State<T> getCurrentState() {
        try {
            return stateStack.peek();
        } catch (EmptyStackException e) {
            return new State<T>(null);
            //FIXME
        }
    }

    /**
     * Create new state containing goals and selected goal node an push to stack
     *
     * @param goals
     * @param selected
     * @return state that is pushed to stack
     */
    public State<T> newState(List<GoalNode<T>> goals, GoalNode<T> selected) {
        if (selected != null && !goals.contains(selected)) {
            throw new IllegalStateException("selected goal not in list of goals");
        }
        return pushState(new State<>(goals, selected));
    }

    /**
     * Cretae a ew state conatining the goals but without selected goal node and push to stack
     *
     * @param goals
     * @return
     */
    public State<T> newState(List<GoalNode<T>> goals) {
        return newState(goals, null);
    }

    /**
     * Cretae a new state containing only the selected goal node and push to stack
     *
     * @param selected
     * @return reference to state on stack
     */
    public State<T> newState(GoalNode<T> selected) {
        return newState(Collections.singletonList(selected), selected);
    }

    /**
     * Push state to stack and return reference to this state
     *
     * @param state
     * @return
     */
    public State<T> pushState(State<T> state) {
        if (stateStack.contains(state)) {
            throw new IllegalStateException("State is already on the stack!");
        }
        stateStack.push(state);
        return state;
    }

    /**
     * Remove top level state from stack and throw an Exception if state does not equal expected state
     *
     * @param expected
     * @return
     */
    public State<T> popState(State<T> expected) {
        State<T> actual = stateStack.pop();
        if (!expected.equals(actual)) {
            throw new IllegalStateException("Error on the stack!");
        }
        return actual;
    }

    /**
     * Remove top level state from stack
     *
     * @return
     */
    protected State<T> popState() {
        return stateStack.pop();
    }

    /**
     * Lookup state on the stack but do not remove it
     *
     * @return
     */
    public State<T> peekState() {
        return stateStack.peek();
    }

    //endregion

    /**
     * Get goalnodes from current state
     *
     * @return
     */
    public List<GoalNode<T>> getCurrentGoals() {
        return getCurrentState().getGoals();
    }

}
