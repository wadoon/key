package de.uka.ilkd.key.kexext.backgroundSMT;

import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;

public class BackgroundSMTProblem {

    private final SMTProblem problem;
    private final BackgroundSolverRunner runner;
    private final SolverLauncher launcher;

    public BackgroundSMTProblem(SMTProblem problem, BackgroundSolverRunner runner, SolverLauncher launcher) {
        this.problem = problem;
        this.runner = runner;
        this.launcher = launcher;
    }

    public SMTProblem getProblem() {
        return problem;
    }

    public SolverLauncher getLauncher() {
        return launcher;
    }

    public BackgroundSolverRunner getRunner() {
        return runner;
    }
}
