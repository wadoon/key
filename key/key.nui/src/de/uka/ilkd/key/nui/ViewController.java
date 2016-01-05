package de.uka.ilkd.key.nui;

import javafx.embed.swing.SwingNode;
import javafx.fxml.Initializable;

public abstract class ViewController implements Initializable {

    protected Context context;
    protected MainApp mainApp;

    public void setMainApp(MainApp mainApp, Context context) {
        this.mainApp = mainApp;
        this.context = context;
        initializeAfterLoadingFxml();
    }

    public abstract void initializeAfterLoadingFxml();
    
    public abstract void createSwingContent(final SwingNode swingNode);
}