package edu.kit.iti.formal.psdbg.parser.function;

import lombok.Getter;

import java.util.HashMap;
import java.util.Map;
import java.util.ServiceLoader;

/**
 * @author Alexander Weigl
 * @version 1 (10.11.17)
 */
@Getter
public class FunctionRegister {
    private Map<String, ScriptFunction> functions = new HashMap<>();

    public static FunctionRegister getDefault() {
        return new FunctionRegister().loadDefault();
    }

    /**
     * Load the default script functions via {@link java.util.ServiceLoader}.
     */
    public FunctionRegister loadDefault() {
        ServiceLoader<ScriptFunction> sf = ServiceLoader.load(ScriptFunction.class);
        sf.forEach(s -> put(s.getName(), s));
        return this;
    }

    public int size() {
        return functions.size();
    }

    public boolean isEmpty() {
        return functions.isEmpty();
    }

    public boolean containsKey(String key) {
        return functions.containsKey(key);
    }

    public boolean containsValue(ScriptFunction value) {
        return functions.containsValue(value);
    }

    public ScriptFunction get(String key) {
        return functions.get(key);
    }

    public ScriptFunction put(String key, ScriptFunction value) {
        return functions.put(key, value);
    }

    public ScriptFunction remove(String key) {
        return functions.remove(key);
    }
}
