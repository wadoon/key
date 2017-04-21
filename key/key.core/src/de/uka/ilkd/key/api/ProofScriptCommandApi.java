package de.uka.ilkd.key.api;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptCommand;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public class ProofScriptCommandApi {
    private Map<String, ProofScriptCommand> commandMap = new HashMap<>();

    public ProofScriptCommandApi() {

    }

    /**
     *
     * @return
     */
    public Collection<ProofScriptCommand> getScriptCommands() {
        return commandMap.values();
    }

    /**
     *
     * @param name
     * @return
     */
    public ProofScriptCommand getScriptCommands(String name) {
        return commandMap.get(name);
    }
}
