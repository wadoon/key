package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.Term;

public class FilteringTermTraverser {

    private Condition cond;
    private Permutation permutation;
    private Set<Term> terms;

    private FilteringTermTraverser(Condition cond, Permutation permutation) {
        this.cond = cond;
        this.permutation = permutation;
        this.terms = new HashSet<Term>();
    }

    private void filter(Term term) {
        if (cond.decide(term))
            terms.add(permutation.permute(term));
        term.subs().forEach(sub -> filter(sub));
    }

    private Set<Term> getResult() {
        return terms;
    }

    public static Set<Term> filter(Term term, Condition cond, Permutation permutation) {
        FilteringTermTraverser traverser = new FilteringTermTraverser(cond, permutation);
        traverser.filter(term);
        return traverser.getResult();
    }

    public interface Permutation {
        Term permute(Term t);
    }

    public interface Condition {
        boolean decide(Term t);
    }

}
