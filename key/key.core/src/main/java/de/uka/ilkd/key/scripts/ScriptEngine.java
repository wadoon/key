package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Proof;

/**
 * @author Alexander Weigl
 * @version 1 (11/3/20)
 */
public interface ScriptEngine {
    void execute();

    String getDialect();

    ScriptEngine script(String first);

    ScriptEngine proof(Proof proof);

    ScriptEngine origin(Location second);

    ScriptEngine ui(AbstractUserInterfaceControl ui);
}
