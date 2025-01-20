/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.nparser.ParsingFacade;
import org.antlr.v4.runtime.CharStreams;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;

/**
 * Call other script files.
 */
public class ScriptCommand extends AbstractCommand<ScriptCommand.Parameters> {
    private static final Logger LOGGER = LoggerFactory.getLogger(ScriptCommand.class);

    public ScriptCommand() {
        super(Parameters.class);
    }

    public static class Parameters {
        @Option("#2")
        public String filename;
    }

    @Override
    public void execute(Parameters args) throws ScriptException, InterruptedException {
        File root = state.getBaseFileName();
        if (!root.isDirectory()) {
            root = root.getParentFile();
        }
        Path file = root.toPath().resolve(args.filename);

        LOGGER.info("Included script {}", file);

        try {
            var script = ParsingFacade.parseProofScript(CharStreams.fromPath(file));
            ProofScriptEngine pse = new ProofScriptEngine(script);
            pse.setCommandMonitor(state.getObserver());
            pse.execute(uiControl, proof);
        } catch (NoSuchFileException e) {
            // The message is very cryptic otherwise.
            throw new ScriptException("Script file '" + file + "' not found", e);
        } catch (Exception e) {
            throw new ScriptException("Error while running script'" + file + "': " + e.getMessage(),
                    e);
        }
    }

    @Override
    public String getName() {
        return "script";
    }
}
