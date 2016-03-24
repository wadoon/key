package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import javafx.fxml.FXML;

/**
 * This sequent view does not change when a node is selected in the tree. The
 * displayed sequent only changes if a rule is applied directly in this sequent
 * view.
 * 
 * @author Victor Schuemmer
 * @author Maximilian Li
 * @version 1.0
 */
public class StaticSequentViewController extends ViewController {
    @FXML
    private SequentViewController sequentViewController;

    /**
     * @return the {@link SequentViewController controller} of the embedded
     *         sequent view
     */
    public SequentViewController getSequentViewController() {
        return sequentViewController;
    }

    private KeYMediator mediator;

    private Node node;

    /**
     * @return the current {@link Node} of this sequent view
     */
    public Node getNode() {
        return node;
    }
    
    private Proof proof;

    /**
     * @return the current {@link Proof} of this sequent view
     */
    public Proof getProof() {
        return proof;
    }

    private Goal goal;

    /**
     * @return the current {@link Goal} of this sequent view
     */
    public Goal getGoal() {
        return goal;
    }

    private int updateCounter = 0;

    @Override
    public void initializeAfterLoadingFxml() {
        sequentViewController.initViewController(getMainApp(), getContext());

        mediator = getContext().getKeYMediator();

        proof = mediator.getSelectedProof();
        goal = mediator.getSelectedGoal();
        node = mediator.getSelectedNode();

        KeYSelectionListener proofChangeListener = new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                sequentViewController.enableTacletMenu(
                        (mediator.getSelectedProof() == getProof())
                                && (mediator.getSelectedGoal() == getGoal()));
            }

            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                // Only Update the StaticSequentView, if the ProofUpdate was
                // triggered within the same StaticSequentView itself and
                // the Goal is the same OR a GoalChange was triggered by the
                // RuleApplication in the StaticSequentView itself\\
                // (= updateCounter > 0)
                if (sequentViewController
                        .getLastTacletActionID() == sequentViewController
                                .getOwnID()
                        && (goal == mediator.getSelectedGoal()
                                || updateCounter > 0)) {
                    proof = mediator.getSelectedProof();
                    goal = mediator.getSelectedGoal();
                    node = mediator.getSelectedNode();
                    sequentViewController.loadNodeToView(node);

                    // Applying a Rule triggers 3 Update Steps. To let the
                    // static SequentView update, use the stepCounter.\\
                    // Else it remains completely static or \\
                    // You cannot Counteract GoalChanges -> Exception!
                    updateCounter++;
                    if (updateCounter == 3) {
                        updateCounter = 0;
                        sequentViewController.setLastTacletActionID(-1);
                    }
                }
                // If LastAction was registered, but no Change Applied, remove
                // LastAction
                else if (sequentViewController
                        .getLastTacletActionID() == sequentViewController
                                .getOwnID()) {
                    sequentViewController.setLastTacletActionID(-1);
                }
            }
        };

        // TODO is this still needed?
        proof.addProofTreeListener(new ProofTreeListener() {

            @Override
            public void smtDataUpdate(ProofTreeEvent e) {
            }

            @Override
            public void proofStructureChanged(ProofTreeEvent e) {
            }

            @Override
            public void proofPruned(ProofTreeEvent e) {
                // TODO what happens in this if case?
                if (e.getNode().find(node)) {
                }
            }

            @Override
            public void proofIsBeingPruned(ProofTreeEvent e) {
            }

            @Override
            public void proofGoalsChanged(ProofTreeEvent e) {
                if (e.getGoal() == goal) {
                    Node target = node;
                    while (node.subtreeIterator().hasNext()) {
                        target = node.subtreeIterator().next();
                    }
                    sequentViewController.loadNodeToView(target);
                }
            }

            @Override
            public void proofGoalsAdded(ProofTreeEvent e) {
            }

            @Override
            public void proofGoalRemoved(ProofTreeEvent e) {
                if (e.getGoal() == goal) {
                    sequentViewController.enableTacletMenu(false);
                    mediator.removeKeYSelectionListener(proofChangeListener);
                }
            }

            @Override
            public void proofExpanded(ProofTreeEvent e) {
            }

            @Override
            public void proofClosed(ProofTreeEvent e) {
                sequentViewController.enableTacletMenu(false);
                mediator.removeKeYSelectionListener(proofChangeListener);
            }
        });

        mediator.addKeYSelectionListener(proofChangeListener);
    }

}
