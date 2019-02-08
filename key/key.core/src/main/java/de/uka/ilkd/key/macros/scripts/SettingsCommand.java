package de.uka.ilkd.key.macros.scripts;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;

/**
 * This command is used to set variables in the proof environment.
 *
 * @author Alexander Weigl
 * @version 1 (11.05.17)
 */
public class SettingsCommand
        extends AbstractCommand<SettingsCommand.Parameters> {

    /** The parameters of this command. */
    public static class Parameters {
        /** OSS on/off parameter */
        @Option(value = "oss", required = false)
        public Boolean oneStepSimplification;
        /** number of proof steps parameter */
        @Option(value = "steps", required = false)
        public Integer proofSteps;
        /** Variable other parameters */
        @Varargs
        public Map<String, String> others = new LinkedHashMap<>();
    }

    public SettingsCommand() {
        super(Parameters.class);
    }

    @Override
    protected void execute(Parameters args)
            throws ScriptException, InterruptedException {
        if (args.oneStepSimplification != null) {
            //@formatter:off
//            proof.getProofIndependentSettings().getGeneralSettings() FIXME: non-executable code
//                    .setOneStepSimplification(args.oneStepSimplification);
            //@formatter:on

            log.info(String.format("Set oneStepSimplification to %s",
                    args.oneStepSimplification));
        }

        if (args.proofSteps != null) {
            proof.getSettings().getStrategySettings()
                    .setMaxSteps(args.proofSteps);
        }
    }

    @Override
    public String getName() {
        return "set";
    }
}
