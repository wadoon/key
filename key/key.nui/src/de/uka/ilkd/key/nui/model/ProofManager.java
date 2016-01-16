package de.uka.ilkd.key.nui.model;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.nui.MediatorUserInterface;
import de.uka.ilkd.key.nui.util.IStatusManager;

/**
 * Provides a wrapper of the KeYMediator
 * with basic loading of proofs
 * @author Benedikt Gross
 * @author Nils Muzzulini
 *
 */
public class ProofManager {
    private IStatusManager statusManager;
    private List<IProofListener> listeners = new ArrayList<IProofListener>();
    private KeYMediator mediator;

    public KeYMediator getMediator() {
        return mediator;
    }

    /**
     * Creates a new Proofmanager.
     * 
     * @param statusManager
     *            a StatusManager to print status texts to
     */
    //todo link annot
    public ProofManager(IStatusManager statusManager) {
        this.statusManager = statusManager;
        MediatorUserInterface userInterface = new MediatorUserInterface(statusManager);
        mediator = new KeYMediator(userInterface);
        userInterface.setMediator(mediator);
        mediator.addKeYSelectionListener(new ProofListener());
    }

    public synchronized void addProofListener(IProofListener proofListener) {
        this.listeners.add(proofListener);
    }

    public synchronized void removeProofListener(IProofListener proofListener) {
        this.listeners.remove(proofListener);
    }

    private synchronized void fireProofUpdatedEvent() {
        ProofEvent proofEvent = new ProofEvent(mediator.getSelectedProof());
        Iterator<IProofListener> listeners = this.listeners.iterator();
        while (listeners.hasNext()) {
            ((IProofListener) listeners.next()).proofUpdated(proofEvent);
        }
    }

    /**
     * Load a Proof.
     * 
     * @param file
     *            Proof to be loaded.
     */
    public synchronized void loadProblem(File proofFile) {
        // this.proof.setProofFile(proofFile);
        statusManager.setStatus("Loading Proof...");
        mediator.getUI().loadProblem(proofFile);
        // statusManager.setStatus("Proof loaded: " + proofFile.getName());
        // fireProofUpdatedEvent();
    }

    class ProofListener implements KeYSelectionListener {
        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
            if (mediator.isInAutoMode()) {
                return;
            }
            fireProofUpdatedEvent();
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            //proof = e.getSource().getSelectedProof();
            fireProofUpdatedEvent();
        }
    }
}
