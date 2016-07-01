package org.key_project.common.core.proof;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.calculus.CCSequent;
import org.key_project.common.core.logic.calculus.CCSequentChangeInfo;
import org.key_project.common.core.logic.op.CCProgramVariable;
import org.key_project.common.core.logic.visitors.CCTermVisitor;
import org.key_project.common.core.rule.RuleApp;
import org.key_project.common.core.services.CCServices;
import org.key_project.util.collection.ImmutableList;

/**
 *  A proof is represented as a tree of nodes containing sequents. The initial
 *  proof consists of just one node -- the root -- that has to be
 *  proved. Therefore it is divided up into several sub goals and so on. A
 *  single goal is not divided into sub goals any longer if the contained
 *  sequent becomes an axiom. A proof is closed if all leaves are closed. As
 *  the calculus works only on the leaves of a tree, the goals are the
 *  additional information needed for the proof is only stored at the leaves
 *  (saves memory) and not in the inner nodes. This class represents now a goal
 *  of the proof, this means a leave whose sequent is not closed. It keeps
 *  track of all applied rule applications on the branch and of the
 *  corresponding rule application index. Furthermore it offers methods for
 *  setting back several proof steps. The sequent has to be changed using the
 *  methods of Self.
 */
public interface CCGoal<ProgVar extends CCProgramVariable<?, ?>, 
    T extends CCTerm<?, ?, ? extends CCTermVisitor<T>, T>,
    Seq extends CCSequent<T, ?, Seq>,
    RA extends RuleApp<T, Self>,
    Self extends CCGoal<ProgVar, T, Seq, RA, Self>> {

    /** returns set of rules applied at this branch
     * @return IList<RuleApp> applied rule applications
     */
    ImmutableList<RuleApp<T, Self>> appliedRuleApps();

    /** returns the proof the goal belongs to
     * @return the Proof the goal belongs to
     */
    CCProof<Self> proof();

    /** returns the sequent of the node
     * @return the Seq to be proved
     */
    Seq sequent();

    /**
     * Checks if the goal is enabled (this means rule can be applied)
     *
     * @return true, if the goal is enabled
     */
    boolean isEnabled();
    
    /**
     * Checks if is this node is linked to another
     * node (for example due to a join operation).
     *
     * @return true iff this goal is linked to another node.
     */
    boolean isLinked();

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
    Self getLinkedGoal();

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
    void setLinkedGoal(Self linkedGoal);

    /**
     * sets the sequent of the node
     * @param sci SequentChangeInfo containing the sequent to be set and
     * desribing the applied changes to the sequent of the parent node
     */
    void applySequentChangeInfo(CCSequentChangeInfo<T, Seq> sci);
    
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
    void addAppliedRuleApp(RuleApp<T, Self> app);

    /** creates n new nodes as children of the
     * referenced node and new
     * n goals that have references to these new nodes.
     * @return the list of new created goals.
     */
    ImmutableList<Self> split(int n);

    /** 
     * applies the provided rule application to this goal 
     * 
     * @param ruleApp the {@link RuleApp} to apply
     * @return the result of the application
     */
    ImmutableList<Self> apply(RuleApp<T, Self> ruleApp);

   /** 
    * returns the {@link CCServices} of the {@link Proof} 
    * @return the {@link CCServices}
    */
    CCServices<?, T, ?, ?> getServices();
    
    /**
     * @return the current time of this goal (which is just the number of
     * applied rules)
     */
    long getTime ();

}