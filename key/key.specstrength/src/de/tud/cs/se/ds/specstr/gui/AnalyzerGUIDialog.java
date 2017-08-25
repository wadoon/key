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

import java.net.URL;

import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.layout.AnchorPane;
import javafx.stage.Stage;

/**
 * The standalone GUI {@link Application} for strength analysis.
 *
 * @author Dominic Scheurer
 */
public class AnalyzerGUIDialog extends Application {

    @Override
    public void start(Stage stage) throws Exception {
        final FXMLLoader loader = new FXMLLoader();
        final URL resource = AnalyzerGUIDialog.class
                .getResource("AnalyzerGUI.fxml");

        assert resource != null : "Could not find FXML file for abstraction predicates choice dialog";

        loader.setLocation(resource);
        
        final AnchorPane root = (AnchorPane) loader.load();
        final AnalyzerGUIController controller =
                (AnalyzerGUIController) loader.getController();

        stage.setTitle("Coverage of Specifications Analysis");
        stage.setScene(new Scene(root, 900, 500));
        stage.show();

        controller.setMainWindow(stage);
    }

    public static void main(String[] args) {
        Application.launch(AnalyzerGUIDialog.class, args);
    }
}
