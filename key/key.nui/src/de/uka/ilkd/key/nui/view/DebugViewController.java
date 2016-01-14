package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.fxml.FXML;
import javafx.print.PrintColor;
import javafx.scene.control.TextArea;

@KeYView(title = "Debug", path = "", preferredPosition = ViewPosition.TOPRIGHT)
public class DebugViewController extends ViewController {

    @FXML
    private TextArea outputText;
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        debugViewController = this;
    }
    
    public void Print(String str){
        outputText.setText(str);
    }
    
    private static DebugViewController debugViewController;
    public static void PrintOnCurrent(String str){
        debugViewController.Print(str);
    }
}
