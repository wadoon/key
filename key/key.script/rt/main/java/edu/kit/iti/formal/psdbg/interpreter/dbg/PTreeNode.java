package edu.kit.iti.formal.psdbg.interpreter.dbg;

import edu.kit.iti.formal.psdbg.ShortCommandPrinter;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.parser.ast.CaseStatement;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import lombok.Setter;

import javax.annotation.Nullable;
import java.util.*;
import java.util.stream.Collectors;

/**
 * PTreeNode represents a node in the state graph.
 * <p>
 * This class is visualized by the debugger. Their interdepencies are given via the.
 * </p>
 * A node contains a reference to the ASTNode and a reference to the corresponding interpreter state
 * if this state is already interpreted, null otherwise.
 */
@Getter
@Setter
@RequiredArgsConstructor
public class PTreeNode<T> {
    private final ASTNode statement;

    private Map<CaseStatement, List<GoalNode<T>>> mappingOfCaseToStates = new HashMap<>();

    private State<T> stateBeforeStmt;

    private State<T> stateAfterStmt;

    private ASTNode[] context;

    private boolean atomic;

    private boolean isFirstNode = false;

    private boolean isLastNode = false;

    @Nullable
    private PTreeNode<T> stepInto;

    @Nullable
    private PTreeNode<T> stepOver;

    @Nullable
    private PTreeNode<T> stepInvOver;

    @Nullable
    private PTreeNode<T> stepInvInto;

    @Nullable
    private PTreeNode<T> stepReturn;

    private int order;

    public void connectStepOver(PTreeNode<T> jumpOverTo) {
        setStepOver(jumpOverTo);
        jumpOverTo.setStepInvOver(this);
    }

    public void connectStepInto(PTreeNode<T> jumpIntoTo) {
        setStepInto(jumpIntoTo);
        jumpIntoTo.setStepInvInto(this);
    }

    public List<GoalNode<T>> getActiveGoalsForCase(CaseStatement caseStmt) {
        return mappingOfCaseToStates.getOrDefault(caseStmt, Collections.emptyList());
    }

    public List<PTreeNode<T>> getContextNodes() {
        List<PTreeNode<T>> contextNodes = new ArrayList<>(context.length);
        PTreeNode<T> cur = this;
        outer:
        do {
            // add the current node, and every node that can be reached by an inverse into pointer.
            contextNodes.add(cur);

            // if the current node doesn't have an inverse into pointer, then trace
            // inverse over pointer (same context)
            while (cur.getStepInvInto() == null) {
                cur = cur.getStepInvOver();
                if (cur == null) break outer; // we could reach the beginning of execution
            }
            cur = cur.getStepInvInto();
        } while (cur != null);
        return contextNodes;
    }

    public String getSingleRepresentation() {
        if (getStatement().getStartPosition() != null) {
            if (getStatement().getStartPosition().getLineNumber() >= 0) {
                return String.format("%d: %s",
                        getStatement().getStartPosition().getLineNumber(),
                        getStatement().accept(new ShortCommandPrinter()));
            } else {
                return "End of Script";
            }
        } else {
            return (String) getStatement().accept(new ShortCommandPrinter());
        }
    }

    @Override
    public String toString() {
        return getSingleRepresentation();
    }

    /**
     * Calculate a span of bytes of the syntactical representation.
     *
     * @return
     */
    int getSyntaxWidth() {
        return getStatement().getSyntaxWidth();
    }

    public Collection<GoalNode<T>> getMutatedNodes() {
        if (!(statement instanceof CallStatement)) {//TODO better predicate for mutators
            return Collections.emptyList();
        }
        assert stateAfterStmt != null && stateBeforeStmt != null;
        ArrayList<PTreeNode<T>> list = new ArrayList<>();
        GoalNode<T> incoming = stateBeforeStmt.getSelectedGoalNode();

        return stateAfterStmt.getGoals().stream().filter(gn -> gn.getParent().equals(incoming)).collect(Collectors.toList());
    }

}