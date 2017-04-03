package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProverTaskListener;

public class TryCloseCommand
        extends AbstractCommand<TryCloseCommand.TryCloseArguments> {
    static class TryCloseArguments {
        @ValueInjector.Option("steps") Integer steps;
        @ValueInjector.Option("#2") String branch;
    }

    @Override public TryCloseArguments evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return ValueInjector.injection(new TryCloseArguments(), arguments);
    }

    @Override public void execute(TryCloseArguments args)
            throws ScriptException, InterruptedException {

        TryCloseMacro macro = args.steps == null ?
                new TryCloseMacro() :
                new TryCloseMacro(args.steps);

        boolean branch = "branch".equals(args.branch);
        Node target;
        if (branch) {
            target = state.getFirstOpenGoal().node();
        }
        else {
            target = state.getProof().root();
        }

        try {
            macro.applyTo(uiControl, target, null, uiControl);
        }
        catch (Exception e) {
            throw new ScriptException(
                    "tryclose caused an exception: " + e.getMessage(), e);
        }

    }

    @Override public String getName() {
        return "tryclose";
    }
}
