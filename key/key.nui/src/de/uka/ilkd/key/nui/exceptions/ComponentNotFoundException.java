package de.uka.ilkd.key.nui.exceptions;

import de.uka.ilkd.key.nui.NUI;

/**
 * Exception thrown by {@link NUI#getComponent(String)} if component with the
 * given fx:id was not found.
 * 
 * @author Florian Breitfelder
 */
public class ComponentNotFoundException extends NUIException {

    private static final long serialVersionUID = 1L;
    /**
     * TODO
     */
    private final String file;
    /**
     * TODO
     * @return
     */
    public String getFile() {
        return file;
    }
    /**
     * TODO
     * @param file
     */
    public ComponentNotFoundException(final String file) {
        super();
        this.file = file;
    }

    @Override
    public String getMessage() {
        return "Can't load component " + file;

    }

}
