package de.uka.ilkd.key.strategy.conflictbasedinst.termtraverser;

/**
 * Abstract class that executes a method on every visited term and traverses all
 * subterms if a certain condition holds on the term.
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public abstract class AbstractTraverser<T> implements Traverser<T> {

    @Override
    public void traverse(T t) {
        operateOn(t);
        if(traverseChilds(t)) getChilds(t).forEach(s -> traverse(s));
    }

    protected abstract Iterable<T> getChilds(T t);

    protected abstract boolean traverseChilds(T t);

    protected abstract void operateOn(T t);
}
