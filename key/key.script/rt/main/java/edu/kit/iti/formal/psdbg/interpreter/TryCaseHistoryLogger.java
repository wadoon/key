package edu.kit.iti.formal.psdbg.interpreter;

import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.interpreter.dbg.InterpreterObserver;
import edu.kit.iti.formal.psdbg.parser.DefaultASTVisitor;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import lombok.Getter;
import lombok.Setter;

import java.util.ArrayList;
import java.util.List;


/**
 * Logger for Interpreting a try case. If the case was successful,
 * the logged Events can be replayed back to the parent interpreter listeners
 */
public class TryCaseHistoryLogger implements InterpreterObserver {
    private final List<ASTNode> queueNode = new ArrayList<>(1024);
    private final List<State> queueState = new ArrayList<>(1024);
    private final List<Boolean> isEntryEvent = new ArrayList<>(1024);
    @Getter @Setter private Interpreter interpreter;

    @Getter
    private EntryListener entryListener = new EntryListener();
    @Getter
    private ExitListener exitListener = new ExitListener();

    public TryCaseHistoryLogger(Interpreter interpreter) {
        this.interpreter = interpreter;
        install(interpreter);
    }

/*    public void printSequenceOfEvents() {
        for (int i = 0; i < sequenceOfEvents.size(); i++) {
            Pair<EntryName, ASTNode> entryNameASTNodePair = sequenceOfEvents.get(i);
            System.out.println(entryNameASTNodePair.getKey() + " " + entryNameASTNodePair.getValue().getStartPosition());

        }
    }
*/

    public void replayEvents(List<Visitor> entry, List<Visitor> exit) {
        for (int i = 0; i < queueState.size(); i++) {
            interpreter.pushState(queueState.get(i));
            ASTNode node = queueNode.get(i);
            if (isEntryEvent.get(i))
                entry.forEach(node::accept);
            else
                exit.forEach(node::accept);
            interpreter.popState(queueState.get(i));
        }
    }

    private void createNewEntry(ASTNode node, State state, boolean b) {
        isEntryEvent.add(b);
        queueNode.add(node);
        queueState.add(state.copy());
    }

    private class EntryListener extends DefaultASTVisitor<Void> {
        @Override
        public Void defaultVisit(ASTNode node) {
            createNewEntry(node, interpreter.peekState(), true);
            return null;
        }
    }


    private class ExitListener extends DefaultASTVisitor<Void> {
        @Override
        public Void defaultVisit(ASTNode node) {
            createNewEntry(node, interpreter.peekState(), false);
            return null;
        }
    }

}
