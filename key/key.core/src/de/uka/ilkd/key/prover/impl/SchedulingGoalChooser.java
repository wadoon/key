package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.prover.GoalChooser;

public interface SchedulingGoalChooser extends GoalChooser {

    void schedule();

    boolean noTasksAvailable();

}