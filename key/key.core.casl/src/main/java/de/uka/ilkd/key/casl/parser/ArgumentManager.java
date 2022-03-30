package de.uka.ilkd.key.casl.parser;

import java.util.IdentityHashMap;
import java.util.Objects;
import java.util.Stack;

public final class ArgumentManager {
    private static final class Scope extends IdentityHashMap<Class<?>, Object> {
    }

    private Scope newScope = new Scope();
    private final Stack<Scope> scopes = new Stack<>();

    <T> void putArg(Class<T> clazz, T obj) {
        newScope.put(Objects.requireNonNull(clazz), Objects.requireNonNull(obj));
    }

    @SuppressWarnings("unchecked")
    <T> T getArg(Class<T> clazz) {
        return Objects.requireNonNull((T) scopes.peek().get(clazz));
    }

    void pushScope() {
        scopes.push(Objects.requireNonNull(newScope));
        newScope = new Scope();
    }

    void popScope() {
        newScope = Objects.requireNonNull(scopes.pop());
    }
}
