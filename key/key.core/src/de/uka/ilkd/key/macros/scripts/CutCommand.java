package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.rifl.SpecificationEntity;

import java.util.Map;

public class CutCommand extends AbstractCommand<CutCommand.Parameters> {
    private static final Name CUT_TACLET_NAME = new Name("cut");

    public CutCommand() {
        super(Parameters.class);
    }

    static class Parameters {
        @Option("#2") Term formula;
    }

    @Override public String getName() {
        return "cut";
    }

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return state.getValueInjector().inject(new Parameters(), arguments);
    }

    @Override public void execute(AbstractUserInterfaceControl uiControl,
            Parameters args, EngineState state)
            throws ScriptException, InterruptedException {

        Taclet cut = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(CUT_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, args.formula,
                state.getProof().getServices(), true);
        state.getFirstOpenGoal().apply(app);
    }

}
