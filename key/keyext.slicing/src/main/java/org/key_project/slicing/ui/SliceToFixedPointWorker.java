package org.key_project.slicing.ui;

import de.uka.ilkd.key.proof.Proof;
import org.key_project.slicing.AnalysisResults;

import javax.swing.*;
import javax.swing.border.EmptyBorder;
import java.awt.*;
import java.util.function.Consumer;
import java.util.function.Function;

final class SliceToFixedPointWorker extends SwingWorker<Void, Void> {
    public Proof proof;
    private Proof proofToDispose;
    private JButton closeButton;
    private Function<Void, AnalysisResults> analyzeButton;
    private Runnable sliceButton;
    private Runnable doneCallback;

    public SliceToFixedPointWorker(Proof p,
                                   Proof proofToDispose,
                                   JButton closeButton,
                                   Function<Void, AnalysisResults> analyzeButton,
                                   Runnable sliceButton,
                                   Runnable doneCallback) {
        this.proof = p;
        this.proofToDispose = proofToDispose;
        this.closeButton = closeButton;
        this.analyzeButton = analyzeButton;
        this.sliceButton = sliceButton;
        this.doneCallback = doneCallback;
    }

    @Override
    protected Void doInBackground() {
        System.out.println("slice maybe on proof " + System.identityHashCode(proof));
        if (isCancelled()) {
            System.out.println("was cancelled");
            doneCallback.run();
            return null;
        }
        var results = analyzeButton.apply(null);
        System.out.println("have results");
        if (results.usefulStepsNr == results.totalSteps) {
            System.out.println("done");
            doneCallback.run();
        } else {
            if (proofToDispose != null) {
                System.out.println("disposing old proof " + System.identityHashCode(proof));
                proofToDispose.dispose();
            }
            proofToDispose = proof;
            System.out.println("clicking on slice");
            SwingUtilities.invokeLater(() ->
                    sliceButton.run()
            );
        }
        return null;
    }

    @Override
    protected void done() {

    }
}
