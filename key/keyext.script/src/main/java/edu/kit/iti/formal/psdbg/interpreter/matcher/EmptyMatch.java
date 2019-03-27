package edu.kit.iti.formal.psdbg.interpreter.matcher;

import java.util.*;
@Deprecated
public class EmptyMatch implements Matchings {
    public static EmptyMatch INSTANCE = new EmptyMatch();
    // public static Matching EMPTY_MATCH_INSTANCE = new Matching();

    private EmptyMatch() {
    }

    @Override
    public boolean isNoMatch() {
        return false;
    }

    @Override
    public boolean isEmpty() {
        return true;
    }

    @Override
    public void add(String binder, MatchPath term) {
        //throw new IllegalStateException();


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
        ArrayList<Match> l = new ArrayList<Match>();
        l.add(new Match());
       return l;
    }

    @Override
    public Matchings reduceConform(Matchings other) {
        return other;
    }

    @Override
    public String toString() {
        return "{{}}";
    }
}
