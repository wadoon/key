package edu.kit.iti.formal.psdbg.interpreter.matcher;

import java.util.TreeMap;

public class Match extends TreeMap<String, MatchPath> {
    public Match() {
    }

    public Match(Match h1) {
        super(h1);
    }

    public static Match singleton(String binder, MatchPath path) {
        Match m = new Match();
        m.put(binder, path);
        return m;
    }

    public static Match empty() {
        Match m = new Match();
        return m;
    }
}
