package de.uka.ilkd.key.prover.impl;

import java.util.ArrayDeque;
import java.util.IdentityHashMap;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;

/**
 * Multi threading enabled goal chooser, but otherwise really dumb. 
 * 
 * The goal chooser registers to the proof and listens for newly created goals.
 * Each of these goal is immediatley scheduled for execution.
 * 
 * 
 * 
 * @author Richard Bubel
 */
public class MultiCoreChooser implements SchedulingGoalChooser {

    /**
     * Listens for applied rules and registers the new created goal for immediate scheduling 
     */
    final class PopulateGoals implements RuleAppListener {
        @Override
        public void ruleApplied(ProofEvent e) {
            final RuleAppInfo rai = e.getRuleAppInfo ();
            if (rai == null) {
                return;
            }
            updateGoalList(rai.getOriginalNode (), e.getNewGoals());
        }
    }

    /** list of goals to be scheduled */
    private ArrayDeque<Goal> nextList = new ArrayDeque<>();
    /** identity hashmap of currently scheduled goals */
    private IdentityHashMap<Goal,Goal> currentlyScheduled = new IdentityHashMap<>();
    /** the prover to which this goal chooser serves new goals */
    private MultiCoreProver prover;
    /** listener for new goals */
    private PopulateGoals listener;
    /** the proof object */
    private Proof proof;

    /** 
     * creates a new multi core goal chooser for the given prover
     * @param prover the ProverCore
     */
    public MultiCoreChooser(MultiCoreProver prover) {
        this.prover = prover;
    }

    
    @Override
    public void init(Proof p_proof, ImmutableList<Goal> p_goals) {
        this.proof = p_proof;
        if (proof != null) {
            this.listener = new PopulateGoals();
            this.proof.addRuleAppListener(listener);
            insertNewGoals(p_goals);
        }
    }

    @Override
    public Goal getNextGoal() {
        synchronized(nextList) {
            if (nextList.isEmpty()) {
                return null;
            }
            return nextList.pop();
        }
    }

    @Override
    public void removeGoal(Goal p_goal) {
        synchronized(currentlyScheduled) {
            currentlyScheduled.remove(p_goal);
        }
    }

    @Override
    public void updateGoalList(Node node, ImmutableList<Goal> newGoals) {
        insertNewGoals(newGoals);
        schedule();
    }

    private void insertNewGoals(ImmutableList<Goal> newGoals) {
        synchronized(nextList) {
            synchronized(currentlyScheduled) {
                for (final Goal newGoal : newGoals) {
                    if (!currentlyScheduled.containsKey(newGoal)) {
                        nextList.add(newGoal);
                    }
                }
            }
        }
    }

    @Override
    public void schedule() {
        synchronized(currentlyScheduled) {
            synchronized(nextList) {
                while (!nextList.isEmpty()) {
                    final Goal nextGoal = getNextGoal();
                    currentlyScheduled.put(nextGoal, nextGoal);
                    prover.submit(nextGoal);
                }
            }
        }
    }

    @Override
    public void dispose() {
        synchronized(nextList) {
            proof.removeRuleAppListener(listener);
            listener = null;
            currentlyScheduled = null;
            nextList = null;
            prover = null;
        }
    }

    @Override
    public boolean noTasksAvailable() {
        synchronized(currentlyScheduled) {
            synchronized(nextList) {
                return currentlyScheduled.isEmpty() && nextList.isEmpty();
            }
        }
    }

}
