package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import java.util.Map;

public class UnhideCommand extends AbstractCommand<UnhideCommand.Parameters> {
    private static final Name HIDE_LEFT = new Name("hide_left");
    private static final Name HIDE_RIGHT = new Name("hide_right");

    public UnhideCommand() {
        super(Parameters.class);
    }

    @Override
    public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return state.getValueInjector().inject(this, new Parameters(),
                arguments);
    }

    @Override
    public void execute(Parameters args)
            throws ScriptException, InterruptedException {

        Goal goal = state.getFirstOpenAutomaticGoal();

        Taclet hideLeft = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(HIDE_LEFT);
        for (SequentFormula s : args.sequent.antecedent()) {
            TacletApp app = NoPosTacletApp.createNoPosTacletApp(hideLeft);
            SchemaVariable sv = app.uninstantiatedVars().iterator().next();
            app = app.addCheckedInstantiation(sv, s.formula(), service, true);
            goal.apply(app);
        }

        Taclet hideRight = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(HIDE_RIGHT);
        for (SequentFormula s : args.sequent.succedent()) {
            TacletApp app = NoPosTacletApp.createNoPosTacletApp(hideRight);
            SchemaVariable sv = app.uninstantiatedVars().iterator().next();
            app = app.addCheckedInstantiation(sv, s.formula(), service, true);
            goal.apply(app);
        }
    }

    @Override
    public String getName() {
        return "hide";
    }

    public class Parameters {
        /** A formula defining the goal to select */
        @Option("#2")
        public Sequent sequent;
    }

}
