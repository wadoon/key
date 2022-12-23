package de.uka.ilkd.key.kexext.backgroundSMT;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;

import java.awt.event.ActionEvent;
import java.util.*;

public class ApplyBackgroundSolverAction extends KeyAction {

    private BackgroundSolverRunner runner;

    private Map<BackgroundSolverRunner, Boolean> runnerStatus = new HashMap<>();

    public ApplyBackgroundSolverAction() {
        setEnabled(false);
    }

    public void setRunner(BackgroundSolverRunner runner) {
        if (!runnerStatus.keySet().contains(runner)) {
            runnerStatus.put(runner, !runner.getSolvedProblems().isEmpty());
        }
        this.runner = runner;
    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
        if (runner == null) {
            return;
        }
        // copied from SolverListener
        KeYMediator mediator = MainWindow.getInstance().getMediator();
        mediator.stopInterface(true);
        try {
            for (SMTProblem problem : runner.getSolvedProblems()) {
                if (problem.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID) {
                    IBuiltInRuleApp app =
                            RuleAppSMT.rule.createApp(null).setTitle(getTitle(problem));
                    problem.getGoal().apply(app);
                }
            }
            runner.clearSolvedProblems();
        } finally {
            mediator.startInterface(true);
        }
    }

    public void notify(BackgroundSolverRunner runner) {
        runnerStatus.put(runner, !runner.getSolvedProblems().isEmpty());
        setEnabled(runnerStatus.containsValue(true));
    }

    // copied from SolverListener
    private String getTitle(SMTProblem p) {
        String title = "";
        Iterator<SMTSolver> it = p.getSolvers().iterator();
        while (it.hasNext()) {
            title += it.next().name();
            if (it.hasNext()) {
                title += ", ";
            }
        }
        return title;
    }

}
