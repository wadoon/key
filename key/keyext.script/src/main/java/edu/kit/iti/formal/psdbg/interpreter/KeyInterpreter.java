package edu.kit.iti.formal.psdbg.interpreter;

import com.google.common.collect.BiMap;
import com.google.common.collect.ImmutableBiMap;
import de.uka.ilkd.key.api.VariableAssignments;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.interpreter.data.*;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.InvalidTypeException;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.CommandLookup;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.*;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import edu.kit.iti.formal.psdbg.parser.types.TermType;
import edu.kit.iti.formal.psdbg.parser.types.TypeFacade;
import lombok.Getter;

import java.util.List;
import java.util.function.Function;

/**
 * @author Alexander Weigl
 * @version 1 (28.08.17)
 */
public class KeyInterpreter extends Interpreter<KeyData> {
    @Getter
    private static final BiMap<SimpleType, VariableAssignments.VarType> typeConversionBiMap =
            new ImmutableBiMap.Builder<SimpleType, VariableAssignments.VarType>()
                    //              .put(SimpleType.ANY, VariableAssignments.VarType.ANY)
                    .put(SimpleType.BOOL, VariableAssignments.VarType.BOOL)
                    //.put(SimpleType.TERM, VariableAssignments.VarType.FORMULA) //TODO: parametrisierte Terms
                    .put(SimpleType.INT, VariableAssignments.VarType.INT)
                    .put(SimpleType.STRING, VariableAssignments.VarType.OBJECT)
                    //                  .put(SimpleType.INT_ARRAY, VariableAssignments.VarType.INT_ARRAY)
//                    .put(SimpleType.SEQ, VariableAssignments.VarType.SEQ)
                    .build();


    public KeyInterpreter(CommandLookup lookup) {
        super(lookup);
    }


    @Override
    public Object visit(ClosesCase closesCase) {
        /*
        State<KeyData> currentStateToMatch = peekState();
        State<KeyData> currentStateToMatchCopy = currentStateToMatch.copy(); //deepcopy
        GoalNode<KeyData> selectedGoalNode = currentStateToMatch.getSelectedGoalNode();
        GoalNode<KeyData> selectedGoalCopy = currentStateToMatch.getSelectedGoalNode().deepCopy(); //deepcopy
        */
        enterScope(closesCase);
        //execute closesscript
        boolean closed = suspicionExecution(closesCase.getClosesGuard(), true);
        //executeBody(closesCase.getClosesGuard(), selectedGoalNode, new VariableAssignment(selectedGoalNode.getAssignments()));
        //check whether script closed proof
        /*State<KeyData> stateafterIsClosable = peekState();
        List<GoalNode<KeyData>> goals = stateafterIsClosable.getGoals();
        boolean allClosed = true;
        for (GoalNode<KeyData> goal : goals) {
            KeyData data = (KeyData) goal.getData();
            if (!data.getNode().isClosed()) {
                allClosed = false;
                break;
            }
        }
        //prune proof
        LOGGER.debug("The closes script " + (allClosed ? "closed the proof.\n" : "did not close the proof.\n") + "Rolling Back proof now.");
        Proof currentKeYproof = selectedGoalNode.getData().getProof();
        ImmutableList<Goal> subtreeGoals = currentKeYproof.getSubtreeGoals(((KeyData) selectedGoalNode.getData()).getNode());
        currentKeYproof.pruneProof(selectedGoalCopy.getData().getNode());
        popState();
        pushState(currentStateToMatchCopy);
        exitScope(closesCase);
        return allClosed;
        */
        exitScope(closesCase);
        return closed;
    }

    @Override
    public Object visit(TryCase tryCase) {
        enterScope(tryCase);
        boolean b = suspicionExecution(tryCase.getBody(), false);
        exitScope(tryCase);
        return b;
    }


    private boolean suspicionExecution(Statements statements, boolean alwaysPrune) {
        logger.debug(String.format("Beginning of suspicion execution of %s", statements));
        GoalNode<KeyData> goalNode = getSelectedNode();
        pushState(new State<>(goalNode.deepCopy())); // copy for later prove
        List<Visitor> backupExitListener = getExitListeners(),
                backupEntryListener = getEntryListeners();
        try {
            TryCaseHistoryLogger list = new TryCaseHistoryLogger(this);
            executeBody(statements, goalNode, new VariableAssignment(goalNode.getAssignments()));
            State<KeyData> afterExec = peekState();

            boolean allGoalsClosed = peekState().getGoals()
                    .stream()
                    .allMatch(g -> g.getData().getNode().isClosed());
            logger.debug("Ended Side Computation");

            if (!allGoalsClosed || alwaysPrune) {
                logger.debug("Try was not successful, rolling back proof");
                //Throw away the new state, and truncate the prove!
                Proof currentKeYproof = goalNode.getData().getProof();
                Node oldNode = goalNode.getData().getNode();
                //ImmutableList<Goal> subtreeGoals = currentKeYproof.getSubtreeGoals(((KeyData) goalNode.getData()).getNode());
                currentKeYproof.pruneProof(oldNode);
                popState();
                //pushState(goalNode);
            } else {
                //replay all proof events
                //check if state is closed
                //list.printSequenceOfEvents();
                list.replayEvents(backupEntryListener, backupExitListener);
                logger.info("Replaying Events finished");
            }
            return allGoalsClosed;
        } finally {
            exitListeners = backupExitListener;
            entryListeners = backupEntryListener;
        }
    }

    @Override
    protected Evaluator<KeyData> createEvaluator(VariableAssignment assignments, GoalNode<KeyData> g) {
        KeyEvaluator eval = new KeyEvaluator(assignments, g);
        eval.setMatcher(getMatcherApi());
        eval.setTermValueFactory(new Function<TermLiteral, Value>() {
            @Override
            public Value apply(TermLiteral termLiteral) {
                return new Value(TypeFacade.ANY_TERM, new TermValue(termLiteral.getContent()));
            }
        });
        return eval;
    }


    @Override
    public Object visit(LetStatement let) {
        enterScope(let);
        Value value = evaluate(let.getExpression());
        if (!(value.getType() instanceof TermType)) {
            return new InvalidTypeException();
        }

        try {
            TermValue tv = (TermValue) value.getData();
            List<VariableAssignment> vas = getMatcherApi().matchSeq(getSelectedNode(), tv.getTermRepr());
            if (!vas.isEmpty()) {
                VariableAssignment va = vas.get(0);
                if (let.isBindGlobal()) {
                    getSelectedNode().getAssignments().push(va);
                } else {
                    //Path new assignments in chan.
                    va.setParent(getSelectedNode().getAssignments());
                    getSelectedNode().setAssignments(va);

                    let.getBody().accept(this);

                    //remove variables
                    // TODO for all goal nodes, travers VariableAssignment hierarchy
                    // and patch out `va`.
                }
            }
        } catch (ClassCastException e) {
            return new InvalidTypeException(e);
        }
        exitScope(let);
        return null;
    }

}
