package de.uka.ilkd.key.strategy.conflictbasedinst;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Term;

public class DecidingTermTraverser {

    private Condition cond;

    private DecidingTermTraverser(Condition cond) {
        this.cond = cond;
    }

    private boolean traverse(Term term) {
        if(!cond.decide(term)) return false;
        return traverse(term.subs());
    }

    private boolean traverse(ImmutableArray<Term> subs) {
        for(Term sub: subs) {
            if(!traverse(sub)) return false;
        }
        return true;
    }

    public static boolean decide(Term term, Condition cond) {
        DecidingTermTraverser traverser = new DecidingTermTraverser(cond);
        return traverser.traverse(term);
    }

    public interface Condition {
        boolean decide(Term t);
    }

}
