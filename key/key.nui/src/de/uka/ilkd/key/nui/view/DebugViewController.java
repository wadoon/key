package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.viewmediation.DebugViewProxy;
import de.uka.ilkd.key.nui.viewmediation.DereferedViewProxy;
import de.uka.ilkd.key.nui.viewmediation.ViewProxyProvider;
import javafx.fxml.FXML;
import javafx.scene.control.TextArea;

@KeYView(title = "Debug", path = "DebugView.fxml", preferredPosition = ViewPosition.TOPRIGHT)
public class DebugViewController extends ViewController
        implements ViewProxyProvider {

    @FXML
    private TextArea outputText;

    public DebugViewController() {
        proxy = new DebugViewProxy(this);
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
    }

    private DebugViewProxy proxy;

    public void print(String str) {
        outputText.setText(str.replace("\n", "\\n\n"));
    }

    //TOCHECK Method 1
    @Override
    public DereferedViewProxy getProxy() {
        return proxy;
    }
}
