package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Collection;

public interface Filter<T> {
    boolean accept(T t);
    Collection<T> getResult();
}
