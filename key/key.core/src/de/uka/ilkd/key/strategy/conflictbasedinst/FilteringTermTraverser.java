package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Collection;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.conflictbasedinst.termtraverser.TermTraverser;

public class FilteringTermTraverser extends TermTraverser {

    private Filter<Term> filter;

    public FilteringTermTraverser(Filter<Term> filter) {
        this.filter = filter;
    }

    public Collection<Term> getResult() {
        return filter.getResult();
    }

    @Override
    protected boolean traverseChilds(Term t) {
        return true;
    }

    @Override
    protected void operateOn(Term t) {
        if(filter.accept(t));
    }

}
