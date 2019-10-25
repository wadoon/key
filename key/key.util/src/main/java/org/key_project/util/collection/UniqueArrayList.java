package org.key_project.util.collection;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;

/**
 * An {@link ArrayList} where each element occurs exactly once. So to say a set
 * with a fixed order (comparable to {@link LinkedHashSet}), but with all the
 * {@link List} methods, like for accessing elements at fixed positions.
 * 
 * @author Dominic Steinhoefel
 * @param <E> the type of elements in this list
 */
public class UniqueArrayList<E> extends ArrayList<E> {
    private static final long serialVersionUID = 1L;

    /**
     * See {@link ArrayList#ArrayList(int)}
     */
    public UniqueArrayList(int initialCapacity) {
        super(initialCapacity);
    }

    /**
     * See {@link ArrayList#ArrayList()}
     */
    public UniqueArrayList() {
        super();
    }

    @Override
    public boolean add(E e) {
        if (!contains(e)) {
            return super.add(e);
        } else {
            return false;
        }
    }

    @Override
    public void add(int index, E element) {
        if (!contains(element)) {
            super.add(index, element);
        }
    }

    @Override
    public boolean addAll(Collection<? extends E> c) {
        if (c.stream().anyMatch(this::contains)) {
            return false;
        } else {
            return super.addAll(c);
        }
    }

    @Override
    public boolean addAll(int index, Collection<? extends E> c) {
        if (c.stream().anyMatch(this::contains)) {
            return false;
        } else {
            return super.addAll(index, c);
        }
    }
}
