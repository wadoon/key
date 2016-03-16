package de.uka.ilkd.key.nui.exceptions;

import de.uka.ilkd.key.nui.NUI;

/**
 * Exception thrown by {@link NUI#getToggleGroup(String)} if toggle group with
 * the given fx:id was not found.
 * 
 * @author Florian Breitfelder
 */
public class ToggleGroupNotFoundException extends NUIException {

    private static final long serialVersionUID = 1L;

    private String toggleGroup;

    public ToggleGroupNotFoundException(String file) {
        this.toggleGroup = file;
    }

    @Override
    public String getMessage() {
        return "Can't load togglegroup " + toggleGroup;

    }

}
