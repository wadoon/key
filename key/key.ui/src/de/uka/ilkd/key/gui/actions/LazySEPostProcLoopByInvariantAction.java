// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.util.List;
import java.util.Optional;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.InstantiateAbstractExecutionHoleDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.lazyse.InstantiateAbstractExecutionHoleRuleApp;
import de.uka.ilkd.key.rule.lazyse.AbstractExecutionHoleInstantiation;

public final class LazySEPostProcLoopByInvariantAction
        extends MainWindowAction {
    private static final long serialVersionUID = 915588190956945751L;

    private final MainWindow mainWindow;

    public LazySEPostProcLoopByInvariantAction(MainWindow mainWindow) {
        super(mainWindow);
        this.mainWindow = mainWindow;

        setName("Complete by Invariant Reasoning");
        setTooltip("Complete Lazy SE Loop Rule App by Invariant Reasoning");

        getMediator().enableWhenProofLoaded(this);
        getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                if (!getMediator().ensureProofLoaded()) {
                    return;
                }

                final Proof loadedProof = getMediator().getSelectedProof();
                final boolean lazySEProofOptionSet = Optional
                        .ofNullable(
                            loadedProof.getSettings().getChoiceSettings()
                                    .getDefaultChoices().get("lazySymbExec"))
                        .orElse("").equals("lazySymbExec:on");

                LazySEPostProcLoopByInvariantAction.this
                        .setEnabled(lazySEProofOptionSet);
            }
        });

    }

    @Override
    public synchronized void actionPerformed(ActionEvent e) {
        final Proof proof = getMediator().getSelectedProof();
        final InstantiateAbstractExecutionHoleDialog dialog = //
                new InstantiateAbstractExecutionHoleDialog(mainWindow, proof);
        dialog.setVisible(true);

        if (dialog.okPressed()) {
            List<AbstractExecutionHoleInstantiation> insts = dialog.getUserInput();
            for (AbstractExecutionHoleInstantiation inst : insts) {
                for (Goal g : proof
                        .getSubtreeGoals(inst.getAbstractExecutionHole().getProofNode())) {
                    g.apply(new InstantiateAbstractExecutionHoleRuleApp(inst));
                }
            }
        }
    }

}
