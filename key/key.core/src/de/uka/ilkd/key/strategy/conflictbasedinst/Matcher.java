package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.Term;

public class Matcher {

    private LinkedHashSet<CbiPair> results;

    public Matcher() {
        this.results = new LinkedHashSet<CbiPair>();
    }

    public LinkedHashSet<CbiPair> getResults() {
        return results;
    }

    public Term getNextSubstitutionTerm() {
        // TODO Auto-generated method stub
        return null;
    }

}
