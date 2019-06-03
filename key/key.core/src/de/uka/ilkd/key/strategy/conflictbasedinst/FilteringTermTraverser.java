package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.Term;

public class FilteringTermTraverser {

    private Condition cond;
    private Set<Term> terms;

    private FilteringTermTraverser(Condition cond) {
        this.cond = cond;
        this.terms = new HashSet<Term>();
    }

    private void filter(Term term) {
        if(cond.decide(term)) terms.add(term);
        term.subs().forEach(sub -> filter(sub));
    }

    private Set<Term> getResult() {
        return terms;
    }

    public static Set<Term> filter(Term term, Condition cond) {
        FilteringTermTraverser traverser = new FilteringTermTraverser(cond);
        traverser.filter(term);
        return traverser.getResult();
    }

    private interface Condition {
        boolean decide(Term t);
    }

}
