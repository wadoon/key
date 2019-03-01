package edu.kit.iti.formal.psdbg.interpreter.matcher;

import com.google.common.collect.Sets;

import java.util.*;

public interface Matchings {
    public boolean isNoMatch();
    public boolean isEmpty();

    public void add(String binder, MatchPath term);
    public void add(Match singleton);
    public void addAll(Collection<Match> matchings);

    public Collection<Match> getMatchings();

    public Matchings reduceConform(Matchings other);

    default void addAll(Matchings matches) {
        addAll(matches.getMatchings());
    }
}