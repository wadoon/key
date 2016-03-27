package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.fxml.FXML;
import javafx.scene.control.TextArea;

@KeYView(title = "Debug", path = "DebugView.fxml", accelerator = "SHORTCUT + D", preferredPosition = ViewPosition.TOPRIGHT)
public class DebugViewController extends ViewController {

    @FXML
    private TextArea outputText;

    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getSequentHtmlChangedEvent().addHandler(this::print);
    };

    private void print(String str) {
        outputText.setText(str.replace("\n", "\\n\n"));
    }

    @Override
    public void viewSuspended() {
        getContext().getSequentHtmlChangedEvent().removeHandler(this::print);
    }

    @Override
    public void viewReactivated() {
        getContext().getSequentHtmlChangedEvent().addHandler(this::print);
    }
    //TODO: call this 2 methods in ViewInformation on setIsActive or something like that
}
