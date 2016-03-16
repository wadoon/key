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

    private String file;

    public ComponentNotFoundException(String file) {
        this.file = file;
    }

    @Override
    public String getMessage() {
        return "Can't load component " + file;

    }

}
