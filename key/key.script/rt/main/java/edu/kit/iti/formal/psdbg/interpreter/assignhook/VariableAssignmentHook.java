package edu.kit.iti.formal.psdbg.interpreter.assignhook;

import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;

/**
 * @author Alexander Weigl
 * @version 1 (21.08.17)
 */
public interface VariableAssignmentHook<T> {
    /**
     * @param data
     * @param variableName
     * @param value
     * @param <S>
     */
    <S> boolean handleAssignment(T data, String variableName, Value<S> value);

    /**
     * @param data
     * @return
     */
    VariableAssignment getStartAssignment(T data);
}
