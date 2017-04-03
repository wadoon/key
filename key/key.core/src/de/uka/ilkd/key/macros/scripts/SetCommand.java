package de.uka.ilkd.key.macros.scripts;

import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

public class SetCommand extends AbstractCommand<SetCommand.Parameters> {

    static class Parameters {
        @ValueInjector.Option("key") String key;
        @ValueInjector.Option("value") String value;

        public Properties getProperties() {
            Properties p = new Properties();
            p.setProperty(key, value);
            return p;
        }
    }

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return state.getValueInjector().inject(new Parameters(), arguments);
    }

    @Override public void execute(Parameters args)
            throws ScriptException, InterruptedException {
        state.getProof().getSettings().update(args.getProperties());
    }

    @Override public String getName() {
        return "set";
    }
}
