package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.nio.file.NoSuchFileException;
import java.util.Map;
import java.util.Observer;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

public class ScriptCommand extends AbstractCommand<ScriptCommand.Parameters> {

    public static class Parameters {
        @ValueInjector.Option("#2") String filname;
    }

    @Override public void execute(Parameters args)
            throws ScriptException, InterruptedException {
        File root = state.getBaseFileName();
        if (!root.isDirectory())
            root = root.getParentFile();
        File file = new File(root, args.filname);

        System.err.println("Included script " + file);

        try {
            ProofScriptEngine pse = new ProofScriptEngine(file);
            pse.setCommandMonitor(state.getObserver());
            pse.execute(uiControl, proof);
        }
        catch (NoSuchFileException e) {
            // The message is very cryptic otherwise.
            throw new ScriptException("Script file '" + file + "' not found",
                    e);
        }
        catch (Exception e) {
            throw new ScriptException(
                    "Error while running script'" + file + "': " + e
                            .getMessage(), e);
        }
    }

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return ValueInjector.injection(new Parameters(), arguments);
    }

    @Override public String getName() {
        return "script";
    }

}
