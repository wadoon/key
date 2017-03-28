package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (28.03.17)
 */
public abstract class NoArgumentCommand implements ProofScriptCommand<Void> {
    @Override public Void evaluateArguments(EngineState state,
            Map<String, String> arguments) {
        return null;
    }
}
