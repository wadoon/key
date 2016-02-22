package de.uka.ilkd.key.nui.util;

import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;

/**
 * Implementation of the Event pattern. If no parameter should be passed to the
 * event handlers, use EmptyEventArgs.
 * 
 * @author Benedikt Gross
 *
 * @param <T>
 */
public class CsEvent<T> {
    private List<Consumer<T>> listeners = new LinkedList<>();

    /**
     * Add an event handler to this event instance.
     * 
     * @param handler
     */
    public void addHandler(Consumer<T> handler) {
        listeners.add(handler);
    }

    /**
     * Removes an event handler from this event instance
     * 
     * @param listener
     */
    public void removeHandler(Consumer<T> handler) {
        listeners.remove(handler);
    }

    /**
     * Fires this event, notifying all handlers.
     * 
     * @param eventArgs
     *            An object that contains needed information for the event
     *            handlers, or EmptyEventArgs if no information is needed.
     * 
     */
    public void fire(T eventArgs) {
        for (Consumer<T> listener : listeners)
            listener.accept(eventArgs);
    }
}
