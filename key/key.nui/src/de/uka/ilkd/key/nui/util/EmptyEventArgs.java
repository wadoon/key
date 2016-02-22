package de.uka.ilkd.key.nui.util;

/**
 * Representation of no parameter for CsEvents.
 * 
 * @author Benedikt Gross
 *
 */
public final class EmptyEventArgs {

    private EmptyEventArgs() {

    }

    private static EmptyEventArgs args = new EmptyEventArgs();

    public static EmptyEventArgs get() {
        return args;
    }
}
