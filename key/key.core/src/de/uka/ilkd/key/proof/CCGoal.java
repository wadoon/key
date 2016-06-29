package de.uka.ilkd.key.proof;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.calculus.*;
import org.key_project.common.core.logic.op.CCProgramVariable;
import org.key_project.common.core.logic.visitors.CCTermVisitor;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.RuleApp;

public interface CCGoal<ProgVar extends CCProgramVariable<?, ?>, 
    T extends CCTerm<?, ?, ? extends CCTermVisitor<T>, T>,
    SemiSeq extends CCSemisequent<SequentFormula<T>, SemiSeq>,
    Seq extends CCSequent<T, SequentFormula<T>, SemiSeq, Seq>, 
    RA extends RuleApp> {

    /** returns set of rules applied at this branch
     * @return IList<RuleApp> applied rule applications
     */
    ImmutableList<RuleApp> appliedRuleApps();

    /** returns the proof the goal belongs to
     * @return the Proof the goal belongs to
     */
    Proof proof();

    /** returns the sequent of the node
     * @return the Sequent to be proved
     */
    Sequent sequent();

    /**
     * Checks if the goal is enabled (this means rule can be applied)
     *
     * @return true, if the goal is enabled
     */
    boolean isEnabled();

    /**
     * Sets the automatic status of this goal.
     *
     * @param t
     *                the new status: true for automatic, false for interactive
     */
    void setEnabled(boolean t);

    /**
     * Returns the goal that this goal is linked to.
     *
     * @return The goal that this goal is linked to (or null if there is no such one).
     */
    Goal getLinkedGoal();

    /**
     * Sets the node that this goal is linked to; also sets this for
     * all parents.
     * 
     * TODO: Check whether it is problematic when multiple child nodes
     * of a node are linked; in this case, the linkedNode field would
     * be overwritten.
     * 
     * @param linkedGoal The goal that this goal is linked to.
     */
    void setLinkedGoal(Goal linkedGoal);

    /**
     * sets the sequent of the node
     * @param sci SequentChangeInfo containing the sequent to be set and
     * desribing the applied changes to the sequent of the parent node
     */
    void applySequentChangeInfo(CCSequentChangeInfo<T, SequentFormula<T>, SemiSeq, Seq> sci);

    /** adds a formula to the sequent before the given position
     * and informs the rule application index about this change
     * @param cf the SequentFormula<Term> to be added
     * @param p PosInOccurrence<Term, SequentFormula<Term>> encodes the position
     */
    void addFormula(SequentFormula<Term> cf,
            PosInOccurrence<Term, SequentFormula<Term>> p);

    /** adds a formula to the antecedent or succedent of a
     * sequent. Either at its front or back
     * and informs the rule application index about this change
     * @param cf the SequentFormula<Term> to be added
     * @param inAntec boolean true(false) if SequentFormula<Term> has to be
     * added to antecedent (succedent)
     * @param first boolean true if at the front, if false then cf is
     * added at the back
     */
    void addFormula(SequentFormula<Term> cf, boolean inAntec, boolean first);

    /**
     * replaces a formula at the given position
     * and informs the rule application index about this change
     * @param cf the SequentFormula<Term> replacing the old one
     * @param p the PosInOccurrence<Term, SequentFormula<Term>> encoding the position
     */
    void changeFormula(SequentFormula<Term> cf,
            PosInOccurrence<Term, SequentFormula<Term>> p);

    /**
     * Adds a partial instantiated {@link RuleApp} to the available rules 
     * @param app the partial instantiated RuleApp
     */
    void addPartialInstantiatedRuleApp(RA app);

    void addProgramVariable(ProgVar pv);

    /**
     * puts a RuleApp to the list of the applied rule apps at this goal
     * and stores it in the node of the goal
     * @param app the applied rule app
     */
    void addAppliedRuleApp(RuleApp app);

    /** creates n new nodes as children of the
     * referenced node and new
     * n goals that have references to these new nodes.
     * @return the list of new created goals.
     */
    ImmutableList<Goal> split(int n);

    /** 
     * applies the provided rule application to this goal 
     * 
     * @param ruleApp the {@link RuleApp} to apply
     * @return the result of the application
     */
    ImmutableList<Goal> apply(RuleApp ruleApp);

    /** removes a formula at the given position from the sequent
     * and informs the rule appliccation index about this change
     * @param p PosInOccurrence<Term, SequentFormula<Term>> encodes the position
     */
   void removeFormula(PosInOccurrence<T, SequentFormula<T>> p);

    Services getServices();

}