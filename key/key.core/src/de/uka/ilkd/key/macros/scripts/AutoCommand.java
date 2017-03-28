package de.uka.ilkd.key.macros.scripts;

import java.util.Map;
import java.util.Optional;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.Profile;

/**
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public class AutoCommand implements ProofScriptCommand<AutoCommand.Parameters> {

    @Override public String getName() {
        return "auto";
    }

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) {
        Parameters args = new Parameters();
        try {
            ValueInjector.getInstance().inject(args, arguments);
        }
        catch (Exception e) {
            e.printStackTrace();
        }
        return args;
    }

    @Override public void execute(AbstractUserInterfaceControl uiControl,
            Parameters arguments, EngineState state)
            throws ScriptException, InterruptedException {

        Profile profile = state.getProof().getServices().getProfile();

        //
        // create the rule application engine
        final ApplyStrategy applyStrategy = new ApplyStrategy(
                profile.getSelectedGoalChooserBuilder().create());

        //
        // find the targets
        ImmutableList<Goal> goals;
        if (arguments.isOnAllOpenGoals()) {
            goals = state.getProof().openGoals();
        }
        else {
            goals = ImmutableSLList.<Goal>nil()
                    .prepend(state.getFirstOpenGoal());
        }

        //
        // set the max number of steps if given
        int oldNumberOfSteps = state.getMaxAutomaticSteps();
        state.setMaxAutomaticSteps(
                arguments.getSteps().orElse(oldNumberOfSteps));

        //
        // Give some feedback
        applyStrategy.addProverTaskObserver((ProverTaskListener) uiControl);
        // TODO get rid of that cast.

        //
        // start actual autoprove
        try {
            for (Goal goal : goals) {
                applyStrategy.start(state.getProof(),
                        ImmutableSLList.<Goal>nil().prepend(goal));

                // only now reraise the interruption exception
                if (applyStrategy.hasBeenInterrupted()) {
                    throw new InterruptedException();
                }

            }
        }
        finally {
            state.setMaxAutomaticSteps(oldNumberOfSteps);
        }
    }

    static class Parameters {
        @ValueInjector.Option("all") boolean onAllOpenGoals = false;

        @ValueInjector.Option("steps") Optional<Integer> maxSteps = Optional
                .empty();

        public boolean isOnAllOpenGoals() {
            return onAllOpenGoals;
        }

        public void setOnAllOpenGoals(boolean onAllOpenGoals) {
            this.onAllOpenGoals = onAllOpenGoals;
        }

        public Optional<Integer> getSteps() {
            return maxSteps;
        }

    }
}
