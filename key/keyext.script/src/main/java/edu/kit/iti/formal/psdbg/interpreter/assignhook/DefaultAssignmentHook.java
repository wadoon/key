package edu.kit.iti.formal.psdbg.interpreter.assignhook;

import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import lombok.Getter;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * @author Alexander Weigl
 * @version 1 (21.08.17)
 */
public abstract class DefaultAssignmentHook<T> implements VariableAssignmentHook<T> {
    private static Logger logger = LogManager.getLogger(DefaultAssignmentHook.class);

    @Getter
    private final HashMap<String, Variable> variables = new HashMap<>();

    protected <K> Variable register(String varName, String doc, BiFunction<T, Value<K>, Boolean> setter, Function<T, Value<K>> getter) {
        return register(new Variable<>(varName, doc, getter, setter));
    }

    protected <K> Variable register(String varName, BiFunction<T, Value<K>, Boolean> setter, Function<T, Value<K>> getter) {
        return register(new Variable<>(varName, null, getter, setter));
    }

    protected <K> Variable register(Variable<T, K> var) {
        return variables.put(var.name, var);
    }

    @Override
    @SuppressWarnings("unchecked")
    public <S> boolean handleAssignment(T data, String variableName, Value<S> value) {
        if (variables.containsKey(variableName)) {
            Variable<T, S> variable = (Variable<T, S>) variables.get(variableName);
            return variable.setter.apply(data, value);
        }
        //@AW: TODO was true: Why?
        return false;
    }


    @Override
    @SuppressWarnings("unchecked")
    public VariableAssignment getStartAssignment(T data) {
        VariableAssignment va = new VariableAssignment();
        for (Variable<T, ?> var : variables.values()) {
            Value val = var.init.apply(data);
            va.declare(var.name, val.getType());
            va.assign(var.name, val);
        }
        return va;
    }

    @lombok.Value
    public static class Variable<T, K> {
        String name, documentation;
        Function<T, Value<K>> init;
        BiFunction<T, Value<K>, Boolean> setter;
    }
}
