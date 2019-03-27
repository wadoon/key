package edu.kit.iti.formal.psdbg.interpreter.data;

import lombok.Getter;
import lombok.Setter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Object representing a state
 *
 * @author S.Grebing
 */

public class State<T> {

    /**
     * All goalnodes in this state
     */
    @Getter
    private List<GoalNode<T>> goals;

    /**
     * Currently selected GoalNode
     */
    @Getter
    @Setter
    private GoalNode<T> selectedGoalNode;

    @Getter
    @Setter
    private boolean errorState;

    public State(Collection<GoalNode<T>> goals, GoalNode selected) {
        this.goals = new ArrayList<>(goals);
        this.selectedGoalNode = selected;
        assert selected == null || goals.contains(selected);
    }

    public State(List<GoalNode<T>> goals, int n) {
        this(goals, goals.get(n));
    }

    public State(GoalNode<T> goal) {
        assert goal != null;
        goals = new ArrayList<>();
        goals.add(goal);
        setSelectedGoalNode(goal);
    }

    /**
     * creates a state with no goals.
     */
    public State() {
        goals = new ArrayList<>();
        setSelectedGoalNode(null);
    }


    public List<GoalNode<T>> getGoals() {
        return goals;
    }

    /**
     * Deep Copy state
     *
     * @return
     */
    public State<T> copy() {
        List<GoalNode<T>> copiedGoals = new ArrayList<>();
        GoalNode<T> refToSelGoal = null;
        if (goals.size() == 1) {
            GoalNode<T> deepcopy = goals.get(0).deepCopy();
            refToSelGoal = deepcopy;
            copiedGoals.add(deepcopy);
        } else {
            for (GoalNode<T> goal : goals) {
                GoalNode<T> deepcopy = goal.deepCopy();
                copiedGoals.add(deepcopy);

                if (selectedGoalNode != null && goal.equals(getSelectedGoalNode())) {
                    refToSelGoal = deepcopy;
                }
            }
        }
        return new State<T>(copiedGoals, refToSelGoal);
    }

    public GoalNode<T> getSelectedGoalNode() {
     /*   if (selectedGoalNode == null) {
            throw new IllegalStateException("no selected node");
        } else {
            if (getGoals().size() == 1) {
                selectedGoalNode = getGoals().get(0);
            }
            return selectedGoalNode;
        }*/

        if (getGoals().size() == 1) {
            selectedGoalNode = getGoals().get(0);
        }

        return selectedGoalNode;
    }

    public void setSelectedGoalNode(GoalNode<T> gn) {
        if (gn != null) {
            assert goals.contains(gn);
        }
        this.selectedGoalNode = gn;
    }

    public String toString() {
        if (selectedGoalNode == null) {
            return "No Goal selected";
        } else {
            return selectedGoalNode.toString();
        }

    }

}

