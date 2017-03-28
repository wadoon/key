package de.uka.ilkd.key.macros.scripts;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import com.sun.xml.internal.ws.api.pipe.Engine;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.SolverTypeCollection;

public class SMTCommand
        extends AbstractCommand<SMTCommand.SMTCommandArguments> {
    static class SMTCommandArguments {
        @ValueInjector.Option("solver") String solver = "Z3";
    }

    private static final Map<String, SolverType> SOLVER_MAP = computeSolverMap();

    @Override public SMTCommandArguments evaluateArguments(EngineState state,
            Map<String, String> arguments) throws ScriptException {
        return ValueInjector.injection(new SMTCommandArguments(), arguments);
    }

    @Override public String getName() {
        return "smt";
    }

    @Override public void execute(SMTCommandArguments args)
            throws ScriptException, InterruptedException {
        SolverTypeCollection su = computeSolvers(args.solver);

        Goal goal = state.getFirstOpenGoal();

        SMTSettings settings = new SMTSettings(
                goal.proof().getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                goal.proof());
        SolverLauncher launcher = new SolverLauncher(settings);
        Collection<SMTProblem> probList = new LinkedList<SMTProblem>();
        probList.add(new SMTProblem(goal));
        launcher.launch(su.getTypes(), probList, goal.proof().getServices());

        for (SMTProblem problem : probList) {
            if (problem.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
                IBuiltInRuleApp app = RuleAppSMT.rule.createApp(null)
                        .setTitle(args.solver);
                problem.getGoal().apply(app);
            }
        }
    }

    private static Map<String, SolverType> computeSolverMap() {
        Map<String, SolverType> result = new HashMap<String, SolverType>();

        for (SolverType type : SolverType.ALL_SOLVERS) {
            result.put(type.getName(), type);
        }

        return Collections.unmodifiableMap(result);
    }

    private SolverTypeCollection computeSolvers(String value) {
        String[] parts = value.split(" *, *");
        List<SolverType> types = new ArrayList<SolverType>();
        for (String name : parts) {
            SolverType type = SOLVER_MAP.get(name);
            if (type != null) {
                types.add(type);
            }
        }
        return new SolverTypeCollection(value, 1, types);
    }

}
