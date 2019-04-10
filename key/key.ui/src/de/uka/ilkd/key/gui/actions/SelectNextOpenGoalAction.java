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
import java.awt.event.KeyEvent;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;

/** Selects the child of the currently selected element in proof-tree 
 */
public final class SelectNextOpenGoalAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 4574270781882014092L;

    /**
     * Creates a new GoalSelectBelowAction.
     * @param mainWindow the main window this action belongs to
     */
    public SelectNextOpenGoalAction(MainWindow mainWindow) {
        super(mainWindow);
        setAcceleratorLetter(KeyEvent.VK_DOWN);
        setName("Select next Open Goal");
        setTooltip("Changes selected goal in the proof-tree to the previous open goal");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        getMediator().getSelectionModel().selectNextOpenGoal();
    }
}
