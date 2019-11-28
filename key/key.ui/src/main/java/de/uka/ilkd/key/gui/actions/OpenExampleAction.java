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
import java.io.File;
import java.util.Optional;

import de.uka.ilkd.key.abstractexecution.refinity.model.AERelationalModel;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.refinity.relational.dialogs.RefinityWindow;

/**
 * Opens a file dialog allowing to select the example to be loaded
 */
public final class OpenExampleAction extends MainWindowAction {
    
    /**
     * 
     */
    private static final long serialVersionUID = -7703620988220254791L;

    public OpenExampleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Load Example");
        setIcon(IconFactory.openExamples(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Browse and load included examples.");
    }
    
    public void actionPerformed(ActionEvent e) {
        KeYFileChooser keYFileChooser =
                KeYFileChooser.getFileChooser("Select file to load proof or problem");
        File file = ExampleChooser.showInstance(Main.getExamplesDir());
        if(file != null) {
            keYFileChooser.selectFile(file);
            
            if (AERelationalModel.fileHasAEModelEnding(file)) {
                final Optional<AERelationalModel> maybeModel = //
                        AERelationalModel.isRelationalModelFile(file);
                if (!maybeModel.isPresent()) {
                    final String errorMessage = "Failed to load " + file.getName();
                    getMediator().notify(new GeneralFailureEvent(errorMessage));
                    getMediator().getUI().reportStatus(this, errorMessage);
                    return;
                }
                
                final AERelationalModel model = maybeModel.get();
                model.setFile(file);
                final RefinityWindow dia = new RefinityWindow(//
                        MainWindow.getInstance(), model);
                dia.setReadonly(true);
                dia.setVisible(true);
            } else {
                mainWindow.loadProblem(file);
            }
        }
    }
}