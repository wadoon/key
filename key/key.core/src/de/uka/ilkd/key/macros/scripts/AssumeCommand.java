package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

public class AssumeCommand extends AbstractCommand {

    private static final Name TACLET_NAME = new Name("UNSOUND_ASSUME");

    @Override
    public String getName() {
        return "assume";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> state) throws ScriptException, InterruptedException {

        Goal goal = getFirstOpenGoal(proof, state);
        Term formula;
        try {
            String formString = args.get("#2");
            formula = toTerm(proof, goal, state, formString, Sort.FORMULA);
        } catch (ParserException e) {
            throw new ScriptException(e);
        }

        Taclet cut = proof.getEnv().getInitConfigForEnvironment().lookupActiveTaclet(TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, formula, proof.getServices(), true);
        goal.apply(app);
    }
}
