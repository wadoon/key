package de.uka.ilkd.key.nui.util;

import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;

public class CsEvent<T> {
    private List<Consumer<T>> listeners = new LinkedList<>();
    
    public void addHandler(Consumer<T> handler){
        listeners.add(handler);
    }
    public void removeListener(Consumer<T> listener){
        listeners.remove(listener);
    }
    
    public void fire(T eventArgs){
        for(Consumer<T> listener : listeners)
            listener.accept(eventArgs);
    }
}
