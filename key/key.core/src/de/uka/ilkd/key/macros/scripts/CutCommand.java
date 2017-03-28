package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import com.sun.xml.internal.ws.api.pipe.Engine;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

public class CutCommand implements ProofScriptCommand<CutCommand.Parameters> {
    private static final Name CUT_TACLET_NAME = new Name("cut");

    static class Parameters {
        @ValueInjector.Option("#2") Term formula;
    }

    @Override public String getName() {
        return "cut";
    }

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) {
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
