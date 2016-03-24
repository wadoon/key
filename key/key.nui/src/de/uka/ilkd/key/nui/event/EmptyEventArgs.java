package de.uka.ilkd.key.nui.event;

/**
 * Representation of no parameter for {@link HandlerEvent HandlerEvents}.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public final class EmptyEventArgs {

    private EmptyEventArgs() {

    }

    private static EmptyEventArgs args = new EmptyEventArgs();

    /**
     * @return empty argument to pass to a {@link HandlerEvent}
     */
    public static EmptyEventArgs get() {
        return args;
    }
}
