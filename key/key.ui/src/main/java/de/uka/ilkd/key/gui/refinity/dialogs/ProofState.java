// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.refinity.dialogs;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.refinity.listeners.DirtyListener;
import de.uka.ilkd.key.gui.refinity.listeners.ProofStateChangedListener;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;

/**
 * @author Dominic Steinhoefel
 */
public class ProofState implements ProverTaskListener, AutoModeListener, DirtyListener {
    private State state = State.NO_PROOF;
    private Proof currProof = null;
    private List<ProofStateChangedListener> listeners = new ArrayList<>();

    public State getState() {
        return state;
    }

    public Optional<Proof> getProof() {
        return Optional.ofNullable(currProof);
    }

    public void setProof(Proof currProof) {
        this.currProof = currProof;
        state = State.PROOF_LOADED;
    }

    public void register(final UserInterfaceControl uic) {
        uic.getProofControl().addAutoModeListener(this);
        uic.addProverTaskListener(this);
    }

    public void addProofStateChangedListener(final ProofStateChangedListener listener) {
        listeners.add(listener);
    }

    public boolean removeProofStateChangedListener(final ProofStateChangedListener listener) {
        return listeners.remove(listener);
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        final Proof proof = info.getProof();

        if (currProof == null || proof == null || currProof != proof) {
            return;
        }

        if (info.getSource() instanceof ProblemLoader) {
            setState(State.PROOF_LOADED);
        } else if (info.getSource() instanceof ProverCore) {
            setState(proof.closed() ? State.CLOSED : State.OPEN);
        }
    };

    @Override
    public void autoModeStarted(ProofEvent e) {
        final Proof proof = e.getSource();

        if (currProof == null || proof == null || currProof != proof) {
            return;
        }

        setState(State.RUNNING);
    }

    @Override
    public void autoModeStopped(ProofEvent e) {
        final Proof proof = e.getSource();

        if (currProof == null || proof == null || currProof != proof) {
            return;
        }

        setState(proof.closed() ? State.CLOSED : State.OPEN);
    }

    @Override
    public void dirtyChanged(boolean dirty) {
        if (dirty && state != State.NO_PROOF) {
            setState(State.INCONSISTENT);
            currProof = null;
        }
    }

    private void setState(State state) {
        this.state = state;
        changed();
    }

    private void changed() {
        listeners.forEach(l -> l.proofStateChanged(this));
    }

    @Override
    public String toString() {
        return state == State.OPEN ? //
                String.format("%d Open Goals", currProof.openGoals().size()) : //
                state.toString();
    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
    }

    @Override
    public void taskProgress(int position) {
    }

    public static enum State {
        NO_PROOF("No Proof"), //
        PROOF_LOADED("Proof loaded"), //
        RUNNING("Running"), //
        INCONSISTENT("No Proof (Model Changed)"), //
        OPEN("Open"), //
        CLOSED("Closed");

        private final String description;

        private State(final String description) {
            this.description = description;
        }

        @Override
        public String toString() {
            return description;
        }
    }
}
