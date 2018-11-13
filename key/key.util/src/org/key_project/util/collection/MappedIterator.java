package org.key_project.util.collection;

import java.util.Iterator;
import java.util.function.Function;

public class MappedIterator<T, U> implements Iterator<U> {
    private Iterator<T> iterator;
    private final Function<T,U> function;

    public MappedIterator(Iterator<T> iterator, Function<T, U> f) {
        this.iterator = iterator;
        this.function = f;
    }

    @Override
    public boolean hasNext() {
        return iterator.hasNext();
    }

    @Override
    public U next() {
        return function.apply(iterator.next());
    }
}
