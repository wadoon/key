package de.uka.ilkd.key.strategy.conflictbasedinst.termtraverser;

import de.uka.ilkd.key.logic.Term;

public abstract class TermTraverser extends AbstractTraverser<Term> {

    @Override
    protected Iterable<Term> getChilds(Term t) {
        return t.subs();
    }

}
