package de.uka.ilkd.key.rule.executor;

import de.uka.ilkd.key.logic.Term;

import org.key_project.common.core.rule.RuleApp;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleAbortException;


/**
 * Executes a Rule with respect to a given instantiation of the schemavariables.
 */
public interface RuleExecutor {
 
    /** 
     * applies the given rule application to the specified goal
     * @param goal the goal that the rule application should refer to.
     * @param ruleApp the rule application that is executed.
     * @return List of the goals created by the rule which have to be
     * proved. If this is a close-goal-taclet ( this.closeGoal () ),
     * the first goal of the return list is the goal that should be
     * closed (with the constraint this taclet is applied under).
     */
    public abstract ImmutableList<Goal> apply(Goal goal, RuleApp<Term, Goal> ruleApp) throws RuleAbortException;

}
