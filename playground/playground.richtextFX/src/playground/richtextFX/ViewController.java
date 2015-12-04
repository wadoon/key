package playground.richtextFX;

import javafx.fxml.Initializable;

public abstract class ViewController implements Initializable {
    
    protected MainApp mainApp;
    
    public void setMainApp(MainApp mainApp) {
        this.mainApp = mainApp;
    }
}
