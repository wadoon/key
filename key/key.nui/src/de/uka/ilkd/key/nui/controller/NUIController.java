package de.uka.ilkd.key.nui.controller;

import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.NUI;

public abstract class NUIController {

    /**
     * A reference to the {@link NUI} which manages the main application.
     */
    protected NUI nui = null;
    /**
     * The fx:id of the controller.
     */
    protected String componentName = null;
    /**
     * The filename of the associated FXML file.
     */
    protected String filename = null;
    /**
     * The data model linked to application.
     */
    protected DataModel dataModel = null;
    /**
     * The bundle used for internationalization of text strings.
     */
    protected ResourceBundle bundle = null;

    /**
     * Replaces the usual java constructor, because JavaFX does not allow to use
     * user-defined constructors.
     * 
     * @param nuiRef
     *            A reference to the {@link NUI} which manages the main
     *            application.
     * @param dataModel
     *            The data model linked to application.
     * @param bundle
     *            The bundle used for internationalization of text strings.
     * @param componentName
     *            The fx:id of the controller.
     * @param filename
     *            The filename of the associated FXML file.
     */
    public void constructor(NUI nuiRef, DataModel dataModel,
            ResourceBundle bundle, String componentName, String filename) {
        this.nui = nuiRef;
        this.dataModel = dataModel;
        this.bundle = bundle;
        this.componentName = componentName;
        this.filename = filename;

        init();
    }

    /**
     * This method initializes the controller and can be used to perform actions
     * right after creating the controller.
     */
    protected abstract void init();

}
