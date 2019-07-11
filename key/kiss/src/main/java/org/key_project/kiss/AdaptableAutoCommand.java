package org.key_project.kiss;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.macros.ConfigurableProofMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.scripts.AbstractCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Properties;

/**
 * @author Alexander Weigl
 * @version 1 (12.07.19)
 */
public class AdaptableAutoCommand extends AbstractCommand<AdaptableAutoCommand.Parameters> {
    public AdaptableAutoCommand() {
        super(Parameters.class);
    }

    @Override
    protected void execute(Parameters args) throws ScriptException {
        ProofMacro internal = getMacro(args.macro);
        internal.resetParams();

        ConfigurableProofMacro<ProofMacro> macro = new ConfigurableProofMacro<ProofMacro>(internal) {
            @Override
            public String getName() {
                return "generated_macro";
            }

            @Override
            public String getCategory() {
                return "";
            }

            @Override
            public String getDescription() {
                return "";
            }
        };

        if (args.file != null) {
            File f = new File(args.file);
            Properties p = new Properties();
            try (FileReader fr = new FileReader(f)) {
                p.load(fr);
                macro.getCostAdapter().loadFrom(p);
            } catch (IOException e) {
                throw new ScriptException("tactic file does not exists: " + f);
            }
        }

        Goal g = state.getFirstOpenAutomaticGoal();
        ProofMacroFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, state.getProof());
        try {
            uiControl.taskStarted(new DefaultTaskStartedInfo(
                    TaskStartedInfo.TaskKind.Macro, internal.getName(), 0));
            synchronized (internal) {
                info = internal.applyTo(uiControl, g.node(), null, uiControl);
            }
        } catch (Exception e) {
            throw new ScriptException("Macro '" + args.macro
                    + "' raised an exception: " + e.getMessage(), e);
        } finally {
            uiControl.taskFinished(info);
            internal.resetParams();
        }
    }

    private ProofMacro getMacro(String macro) throws ScriptException {
        for (ProofMacro m : KeYApi.getMacroApi().getMacros()) {
            if (m.getName().equals(macro)) {
                return m;
            }
        }
        throw new ScriptException("Could not find macro: " + macro);
    }

    @Override
    public String getName() {
        return "flex-auto";
    }

    class Parameters {
        @Option(value = "maxSteps", required = false)
        int maxSteps = 1000;

        @Option(value = "tactic", required = false)
        @Nullable String file;

        @Option(value = "#2", required = false)
        @NotNull String macro = "auto";
    }
}
