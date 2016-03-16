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
 *
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

    @Override
    public void initializeAfterLoadingFxml() {
        sequentViewController.setMainApp(getMainApp(), getContext());

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
                if (e.getNode().find(node)) {}
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
