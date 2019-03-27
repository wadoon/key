package edu.kit.iti.formal.psdbg.interpreter;

import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.parser.DefaultASTVisitor;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import lombok.Getter;
import lombok.RequiredArgsConstructor;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.17)
 */
@RequiredArgsConstructor
public class HistoryListener extends DefaultASTVisitor<Void> {
    @Getter
    private final List<ASTNode> queueNode = new LinkedList<>();
    @Getter
    private final List<State> queueState = new LinkedList<>();

    private final Interpreter interpreter;

    @Override
    public Void defaultVisit(ASTNode node) {
        queueState.add(interpreter.getCurrentState());
        queueNode.add(node);
        return null;
    }

    public State getLastStateFor(ASTNode node) {
        int index = queueNode.lastIndexOf(node);
        if (index == -1)
            return null;
        return queueState.get(index);
    }

    public List<State> getStates(ASTNode node) {
        ArrayList<State> list = new ArrayList<>(queueState.size());
        for (int i = 0; i < queueNode.size(); i++) {
            if (node.equals(queueNode.get(i))) {
                list.add(queueState.get(i));
            }
        }
        return list;
    }


    public List<State> getStates(int caret) {
        ArrayList<State> list = new ArrayList<>(queueState.size());
        int nearestFoundCaret = -1;

        for (int i = 0; i < queueNode.size(); i++) {
            int currentPos = queueNode.get(i).getRuleContext().start.getStartIndex();
            if (currentPos > nearestFoundCaret && currentPos <= caret) {
                list.clear();
                nearestFoundCaret = currentPos;
            }

            if (currentPos == nearestFoundCaret) {
                list.add(queueState.get(i));
            }
        }
        return list;
    }

}
