package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedHashSet;
import java.util.Stack;

import de.uka.ilkd.key.logic.Term;

public class Falsifier {

    private Term formula;
    private boolean polarity;
    private ConstrainedAssignment ca;
    private MatchingConstraints mc;
    private boolean finished;
    private Stack<Falsifier> falsifierStack;
    private Matcher matcher;
    private LinkedHashSet<CbiPair> results;

    public Falsifier(Term formula, boolean polarity, ConstrainedAssignment ca, MatchingConstraints mc) {
        this.formula = formula;
        this.polarity = polarity;
        this.ca = ca;
        this.mc = mc;
        this.finished = false;
        this.falsifierStack = new Stack<Falsifier>();
        this.matcher = null;
    }

    public LinkedHashSet<CbiPair> getResults() {
        return results;
    }

    public Term getNextSubstitutionTerm() {
        if(matcher != null) {
            Term substTerm = matcher.getNextSubstitutionTerm();
            if(substTerm != null) return substTerm;
            results = matcher.getResults();
            return null;
        }
        if(!falsifierStack.isEmpty()) {
            // get next inst from falsifier
        }
        return null;
    }

}
