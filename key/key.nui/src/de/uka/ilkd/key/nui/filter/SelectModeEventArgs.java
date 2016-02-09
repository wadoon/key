package de.uka.ilkd.key.nui.filter;

import java.util.function.Consumer;

import de.uka.ilkd.key.util.Pair;

public class SelectModeEventArgs {
    private Consumer<Criteria<Pair<Integer, String>>> callback;
    public SelectModeEventArgs(Consumer<Criteria<Pair<Integer, String>>> callback){
        this.callback = callback;
    }

    public void executeCallback(Criteria<Pair<Integer, String>> criteria){
        callback.accept(criteria);
    }
}
