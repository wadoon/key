package de.uka.ilkd.key.scripts;

import org.jetbrains.annotations.Nullable;
import org.key_project.util.ServiceLoaderUtil;

import java.util.Objects;
import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (11/3/20)
 */
public final class ScriptEngineFacade {
    private ScriptEngineFacade(){}

    public static @Nullable ScriptEngine createEngineFor(String dialect) {
        Optional<ScriptEngine> engine = ServiceLoaderUtil.stream(ScriptEngine.class)
                .map(it -> {
                    try {
                        return it.newInstance();
                    } catch (InstantiationException | IllegalAccessException e) {
                        e.printStackTrace();
                    }
                    return null;
                })
                .filter(Objects::nonNull)
                .filter(it -> dialect.equals(it.getDialect()))
                .findFirst();
        return engine.orElse(null);
    }
}
