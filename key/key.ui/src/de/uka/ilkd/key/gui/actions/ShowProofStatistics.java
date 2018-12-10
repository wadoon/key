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
import java.util.Comparator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofStatisticsDialog;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.util.Pair;

public class ShowProofStatistics extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -8814798230037775905L;

    public ShowProofStatistics(MainWindow mainWindow) {
        super(mainWindow);
        setName("Show Proof Statistics");
        setIcon(IconFactory.statistics(16));
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        final Proof proof = getMediator().getSelectedProof();
        if (proof == null) {
            mainWindow.notify(new GeneralInformationEvent(
                    "No statistics available.",
                    "If you wish to see the statistics "
                            + "for a proof you have to load one first"));
        }
        else {
            Statistics.HTMLMessage stats = proof.getStatistics().getHTMLMessage();
            ProofStatisticsDialog.show(mainWindow, null, stats);
        }
    }
}