package de.uka.ilkd.key.kexext.backgroundSMT;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentListener;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.Settings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

public class BackgroundSolverRunner implements RuleAppListener, SolverLauncherListener {

    private final Collection<SolverType> solverTypes = new ArrayList<>();
    private final Collection<SMTProblem> solvedProblems = new ArrayList<>();

    private final Collection<SMTProblem> runningProblems = new ArrayList<>();

    private final ApplyBackgroundSolverAction action;

    public BackgroundSolverRunner(ApplyBackgroundSolverAction linkedAction) {
        action = linkedAction;
        // TODO set background solverTypes via settings
        solverTypes.addAll(SolverTypes.getSolverTypes());
    }

    public Collection<SMTProblem> getSolvedProblems() {
        return new ArrayList<>(solvedProblems);
    }


    @Override
    public void ruleApplied(ProofEvent e) {
        Proof proof = e.getSource();
        DefaultSMTSettings settings =
                new DefaultSMTSettings(proof.getSettings().getSMTSettings(),
                        ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                        proof.getSettings().getNewSMTSettings(), proof);
        Collection<SMTProblem> newProblems = new ArrayList<>();
        for (Goal goal : e.getNewGoals()) {
            if (goal.node().getNodeInfo().getInteractiveRuleApplication()) {
                SMTProblem problem = new SMTProblem(goal);
                newProblems.add(problem);
            }
        }
        Thread thread = new Thread(() -> {
            SolverLauncher launcher = new SolverLauncher(settings);
            launcher.addListener(this);
            launcher.launch(solverTypes, newProblems, proof.getServices());
        }, "SMTRunner");
        thread.start();
    }

    @Override
    public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {
        solvedProblems.addAll(
                runningProblems.stream().filter(
                        p -> p.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID)
                        .collect(Collectors.toList()));
        runningProblems.clear();
        action.notify(this);
    }

    @Override
    public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes, SolverLauncher launcher) {
        runningProblems.addAll(problems);
    }

    public void clearSolvedProblems() {
        solvedProblems.clear();
    }

}
