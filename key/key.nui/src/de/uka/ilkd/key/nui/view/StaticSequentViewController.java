/**
 * 
 */
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
 * @author Victor Schuemmer
 * @author Maximilian Li
 */
public class StaticSequentViewController extends ViewController {
    @FXML
    private SequentViewController sequentViewController;

    public SequentViewController getSequentViewController() {
        return sequentViewController;
    }

    private KeYMediator mediator;

    private Node node;

    public Node getNode() {
        return node;
    }

    public void setNode(Node node) {
        this.node = node;
    }

    private Proof proof;

    public Proof getProof() {
        return proof;
    }

    public void setProof(Proof proof) {
        this.proof = proof;
    }

    private Goal goal;

    public Goal getGoal() {
        return goal;
    }

    public void setGoal(Goal goal) {
        this.goal = goal;
    }

    private int updateCounter = 0;

    @Override
    public void initializeAfterLoadingFxml() {
        sequentViewController.initViewController(getMainApp(), getContext());

        mediator = getContext().getKeYMediator();

        setProof(mediator.getSelectedProof());
        setGoal(mediator.getSelectedGoal());
        setNode(mediator.getSelectedNode());

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
                    setProof(mediator.getSelectedProof());
                    setGoal(mediator.getSelectedGoal());
                    setNode(mediator.getSelectedNode());
                    sequentViewController.loadNodeToView(node);

                    // Appplying a Rule triggers 3 Update Steps. To let the
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
