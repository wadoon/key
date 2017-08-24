// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.gui;

import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.layout.AnchorPane;
import javafx.stage.Stage;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class AnalyzerGUIDialog extends Application {

    @Override
    public void start(Stage stage) throws Exception {
        final FXMLLoader loader =
                new FXMLLoader(getClass().getResource("AnalyzerGUI.fxml"));
        final AnchorPane root = (AnchorPane) loader.load();
        final AnalyzerGUIController controller =
                (AnalyzerGUIController) loader.getController();

        stage.setTitle("Strength Analysis");
        stage.setScene(new Scene(root, 800, 500));
        stage.show();
        
        controller.setMainWindow(stage);
    }

    public static void main(String[] args) {
        Application.launch(AnalyzerGUIDialog.class, args);
    }
}
