package de.uka.ilkd.key.macros.scripts;


import de.uka.ilkd.key.control.AbstractUserInterfaceControl;


/**
 * The Exit Command exits the script
 *
 * * It has no parameters.
 */
public class ExitCommand extends NoArgumentCommand {
    @Override public void execute(AbstractUserInterfaceControl uiControl,
            Void args, EngineState stateMap)
            throws ScriptException, InterruptedException {
        throw new InterruptedException(
                "Interruption requested from within script");

    }

    @Override public String getName() {
        return "exit";
    }
}
