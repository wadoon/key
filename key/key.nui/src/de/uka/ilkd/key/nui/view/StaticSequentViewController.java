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
import javafx.application.Platform;
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

    private boolean isPruned = false;

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
                        (mediator.getSelectedProof() == getProof()));
            }

            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                sequentViewController.enableTacletMenu(
                        (mediator.getSelectedProof() == getProof()));
            }
        };

        proof.addProofTreeListener(new ProofTreeListener() {

            @Override
            public void smtDataUpdate(ProofTreeEvent e) {
            }

            @Override
            public void proofStructureChanged(ProofTreeEvent e) {
            }

            @Override
            public void proofPruned(ProofTreeEvent e) {
                if (isPruned) {
                    isPruned = false;
                    Platform.runLater(() -> {
                        getCloseSelfEvent().fire(null);
                    });

                }
            }

            @Override
            public void proofIsBeingPruned(ProofTreeEvent e) {
                if (e.getNode().find(node)) {
                    sequentViewController.enableTacletMenu(false);
                    mediator.removeKeYSelectionListener(proofChangeListener);
                    isPruned = true;
                }
            }

            @Override
            public void proofGoalsChanged(ProofTreeEvent e) {
                if (e.getGoal() == goal) {
                    Node target = node;
                    while (node.subtreeIterator().hasNext()) {
                        target = node.subtreeIterator().next();
                    }
                    sequentViewController.loadNodeToView(goal, target);
                }
            }

            @Override
            public void proofGoalsAdded(ProofTreeEvent e) {
                if (sequentViewController
                        .getLastTacletActionID() == sequentViewController
                                .getOwnID()
                        && mediator.getSelectedProof() == proof) {

                    goal = e.getGoals().head();
                    node = goal.node();
                    proof = mediator.getSelectedProof();

                    sequentViewController.setLastTacletActionID(-1);
                    updateView();
                }
            }

            @Override
            public void proofGoalRemoved(ProofTreeEvent e) {
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

    @Override
    public void onCloseRequest() {
        sequentViewController.onCloseRequest();
    }

    @Override
    public void viewSuspended() {
        sequentViewController.onCloseRequest();
    }

    @Override
    public void viewReactivated() {
        sequentViewController.viewReactivated();
    }

    /**
     * loads new SequentContent Changes Name enables/disables TacletMenu
     * depending on ProofStatus
     */
    private void updateView() {
        getTitleUpdatedEvent().fire(node.serialNr() + ": " + node.name());

        sequentViewController
                .enableTacletMenu(mediator.getSelectedProof() == proof);

        sequentViewController.loadNodeToView(goal, node);
    }
}
