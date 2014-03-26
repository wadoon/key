// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.GuiUtilities;

/**
 * An action to load cached proof. The loaded proof can be reapplied to the currently selected proof.
 * 
 * @author Maria Pelevina
 * (M)
 *
 */
public class LoadCachedProofAction extends MainWindowAction {

	private static final long serialVersionUID = -1288987473276390969L;

    public LoadCachedProofAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Reuse proof");
        setTooltip("Reapply rules from the cached proof to selected problem");
        mainWindow.getMediator().enableWhenProofLoaded(this);
    }
    
    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getMediator().ensureProofLoaded()) {
            KeYFileChooser keYFileChooser = 
                    GuiUtilities.getFileChooser("Select proof to be reused");
            keYFileChooser.setProofFileFilter();
        	
            boolean loaded = keYFileChooser.showOpenDialog(mainWindow);
        	
            if (loaded) {
                File file = keYFileChooser.getSelectedFile();
            	assert file.getName().endsWith(".proof");
            	keYFileChooser.setDefaultFileFilter();
                mainWindow.reuseProof(file);
            }
            
//            final Proof proof = mainWindow.getMediator().getSelectedProof();
//            try {
//                new ProofSaver(proof, filename, de.uka.ilkd.key.gui.Main.INTERNAL_VERSION).save();
//                final String status = "File quicksaved: "+filename;
//                mainWindow.setStatusLine(status);
//                Debug.out(status);
//            } catch (IOException x) {
//                mainWindow.popupWarning("Quicksaving file "+filename+" failed:\n"+x.getMessage(), "Quicksave failed");
//                Debug.out("Quicksaving file "+filename+" failed.",x);
//            }
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }

    }
}