package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;

import java.io.File;
import java.nio.file.NoSuchFileException;
import java.util.Map;

public class ScriptCommand extends AbstractCommand<ScriptCommand.Parameters> {

    public ScriptCommand() {
        super(Parameters.class);
    }

    public static class Parameters {
        @Option("#2") String filename;
    }

    @Override public void execute(Parameters args)
            throws ScriptException, InterruptedException {
        File root = state.getBaseFileName();
        if (!root.isDirectory())
            root = root.getParentFile();
        File file = new File(root, args.filename);

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

    @Override public String getName() {
        return "script";
    }
}
