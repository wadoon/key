package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.*;

public class SMTCommand
        extends AbstractCommand<SMTCommand.SMTCommandArguments> {
    private static final Map<String, SolverType> SOLVER_MAP = computeSolverMap();

    public SMTCommand() {
        super(SMTCommandArguments.class);
    }

    private static Map<String, SolverType> computeSolverMap() {
        Map<String, SolverType> result = new HashMap<String, SolverType>();

        for (SolverType type : SolverType.ALL_SOLVERS) {
            result.put(type.getName(), type);
        }

        return Collections.unmodifiableMap(result);
    }

    @Override public SMTCommandArguments evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return ValueInjector.injection(this, new SMTCommandArguments(), arguments);
    }

    @Override public String getName() {
        return "smt";
    }

    @Override public void execute(SMTCommandArguments args)
            throws ScriptException, InterruptedException {
        SolverTypeCollection su = computeSolvers(args.solver);

        ImmutableList<Goal> goals;
        if (args.all) {
             goals = state.getProof().openGoals();
        } else {
             goals = ImmutableSLList.<Goal>nil().prepend(state.getFirstOpenAutomaticGoal());
        }

        for (Goal goal : goals) {
            runSMT(args, su, goal);
        }
    }

    private void runSMT(SMTCommandArguments args, SolverTypeCollection su, Goal goal) {
        SMTSettings settings = new SMTSettings(
                goal.proof().getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                goal.proof());
        SolverLauncher launcher = new SolverLauncher(settings);
        Collection<SMTProblem> probList = new LinkedList<>();
        probList.add(new SMTProblem(goal));
        TimerListener timerListener = new TimerListener();
        launcher.addListener(timerListener);
        launcher.launch(su.getTypes(), probList, goal.proof().getServices());

        for (SMTProblem problem : probList) {
            if (problem.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
                IBuiltInRuleApp app = RuleAppSMT.rule.createApp(null)
                        .setTitle(args.solver);
                problem.getGoal().apply(app);
            }
        }

        System.err.println("SMT Runtime: " + timerListener.getRuntime() + " ms");
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

    static class SMTCommandArguments {
        @Option("solver")
        public String solver = "Z3";

        @Option(value = "all", required = false)
        public boolean all = false;
    }

    private static class TimerListener implements SolverLauncherListener {
        private long start;
        private long stop;

        @Override
        public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes, SolverLauncher launcher) {
            this.start = System.currentTimeMillis();
        }

        @Override
        public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {
            this.stop = System.currentTimeMillis();
        }

        public long getRuntime() {
            return stop - start;
        }
    }
}
