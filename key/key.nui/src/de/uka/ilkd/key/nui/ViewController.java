package de.uka.ilkd.key.nui;

import java.net.URL;

import de.uka.ilkd.key.nui.util.KeyFxmlLoader;
import javafx.embed.swing.SwingNode;
import javafx.fxml.Initializable;
import javafx.util.Pair;

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

    public <T> Pair<T, ViewController> loadFxmlViewController(URL path) {
        Pair<T, ViewController> pair = KeyFxmlLoader.loadFxml(path);
        pair.getValue().setMainApp(mainApp, context);
        return pair;
    }

    public <T> T loadFxmlFromContext(URL path) {
        return (T) loadFxmlViewController(path).getKey();
    }

    public MainApp getMainApp() {
        return mainApp;
    }

    public Context getContext() {
        return context;
    }
}