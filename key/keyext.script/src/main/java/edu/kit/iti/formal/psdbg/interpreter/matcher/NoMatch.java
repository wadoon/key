package edu.kit.iti.formal.psdbg.interpreter.matcher;

import java.util.Collection;
import java.util.Collections;

public class NoMatch implements Matchings {
    public static NoMatch INSTANCE = new NoMatch();

    private NoMatch() {
    }

    @Override
    public boolean isNoMatch() {
        return true;
    }

    @Override
    public boolean isEmpty() {
        return false;
    }


    @Override
    public void add(String binder, MatchPath term) {
        throw new IllegalStateException();
    }

    @Override
    public void add(Match singleton) {
        throw new IllegalStateException();
    }

    @Override
    public void addAll(Collection<Match> matchings) {
        throw new IllegalStateException();
    }

    @Override
    public Collection<Match> getMatchings() {
        return Collections.emptyList();
    }

    @Override
    public Matchings reduceConform(Matchings other) {
        return this;
    }

    @Override
    public String toString() {
        return "{NOMATCH}";
    }
}
