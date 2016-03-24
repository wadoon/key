package de.uka.ilkd.key.nui.util;

import java.io.IOException;
import java.net.URL;
import javafx.fxml.FXMLLoader;
import javafx.util.Pair;

/**
 * Loader for FXML files.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public class KeyFxmlLoader {

    /**
     * Loads a FXML file and returns its root node and
     * {@link de.uka.ilkd.key.nui.ViewController controller}.
     * 
     * @param path
     *            the path to the FXML file
     * @return pair of the root node and the ViewController of the loaded FXML
     */
    public static <T, C> Pair<T, C> loadFxml(URL path) {
        try {
            // Load main view
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(path);

            T content = loader.load();

            // Give the controller access to the main app.
            C controller = loader.getController();
            return new Pair<T, C>(content, controller);
        }
        catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }
}
