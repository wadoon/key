package edu.kit.iti.formal.psdbg.interpreter;

import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.Signature;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.17)
 */
public interface MatcherApi<T> {
    /**
     *
     * @param currentState
     * @param label
     * @return
     */
    List<VariableAssignment> matchLabel(GoalNode<T> currentState, String label);

    /**
     *
     * @param currentState
     * @param pattern
     * @return
     */
    List<VariableAssignment> matchSeq(GoalNode<T> currentState, String pattern);

}
