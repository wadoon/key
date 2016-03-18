package de.uka.ilkd.key.nui.controller;

import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.NUI;

/**
 * Abstract common base class for all controllers.
 * 
 * @author Florian Breitfelder
 *
 */
public abstract class NUIController {

    /**
     * A reference to the {@link NUI} which manages the main application.
     */
    protected NUI nui;
    /**
     * The fx:id of the controller.
     */
    protected String componentName;
    /**
     * The filename of the associated FXML file.
     */
    protected String filename;
    /**
     * The data model linked to application.
     */
    protected DataModel dataModel;
    /**
     * The bundle used for internationalization of text strings.
     */
    protected ResourceBundle bundle;

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
    public void constructor(final NUI nuiRef, final DataModel dataModel,
            final ResourceBundle bundle, final String componentName, final String filename) {
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
