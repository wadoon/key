package org.key_project.util.collection;

import java.util.*;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * Utilities for Collections.
 *
 * @author Alexander Weigl
 * @version 1 (29.03.19)
 */
public class KeYCollections {
    // =======================================================
    // Methods operating on Arrays
    // =======================================================

    private final static ImmutableList<?> NIL = new ImmutableSLList.NIL<>();

    // =======================================================
    // Methods operating on Collections
    // =======================================================

    /**
     * Concatenates two arrays. The second array may have an entry type that is a
     * subtype of the first one.
     */
    public static <S, T extends S> S[] concat(S[] s1, T[] s2) {
        S[] res = Arrays.copyOf(s1, s1.length + s2.length);
        System.arraycopy(s2, 0, res, s1.length, s2.length);
        return res;
    }

    /**
     * Combine two maps by function application.
     * Values of <code>m0</code> which are not keys of <code>m1</code>
     * are dropped.
     * This implementation tries to use the same implementation of {@link java.util.Map}
     * (provided in Java SE) as <code>m0</code>.
     */
    public static <S, T, U> Map<S, U> apply(Map<S, ? extends T> m0, Map<T, U> m1) {
        Map<S, U> res;
        final int size = Math.min(m0.size(), m1.size());
        // try to use more specific implementation
        if (m0 instanceof java.util.TreeMap)
            res = new java.util.TreeMap<S, U>();
        else if (m0 instanceof java.util.concurrent.ConcurrentHashMap)
            res = new java.util.concurrent.ConcurrentHashMap<S, U>(size);
        else if (m0 instanceof java.util.IdentityHashMap)
            res = new java.util.IdentityHashMap<S, U>(size);
        else if (m0 instanceof java.util.WeakHashMap)
            res = new java.util.WeakHashMap<S, U>(size);
        else res = new HashMap<S, U>(size);

        for (Map.Entry<S, ? extends T> e : m0.entrySet()) {
            final U value = m1.get(e.getValue());
            if (value != null)
                res.put(e.getKey(), value);
        }
        return res;
    }

    /**
     * Join the string representations of a collection of objects into onw
     * string. The individual elements are separated by a delimiter.
     * <p>
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection an arbitrary non-null collection
     * @param delimiter  a non-null string which is put between the elements.
     * @return the concatenation of all string representations separated by the
     * delimiter
     */
    public static String join(Iterable<?> collection, String delimiter) {
        return StreamSupport.stream(collection.spliterator(), false)
                .map(Objects::toString)
                .collect(Collectors.joining(delimiter));
    }

    /**
     * Join the string representations of an array of objects into one
     * string. The individual elements are separated by a delimiter.
     * <p>
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection an arbitrary non-null array of objects
     * @param delimiter  a non-null string which is put between the elements.
     * @return the concatenation of all string representations separated by the
     * delimiter
     */
    public static String join(Object[] collection, String delimiter) {
        return Arrays.stream(collection)
                .map(Objects::toString)
                .collect(Collectors.joining(delimiter));
    }

    /**
     * Takes a string and returns a string which is potentially shorter and
     * contains a sub-collection of the original characters.
     * <p>
     * All alphabetic characters (A-Z and a-z) are copied to the result while
     * all other characters are removed.
     *
     * @param string an arbitrary string
     * @return a string which is a sub-structure of the original character
     * sequence
     * @author mattias ulbrich
     */
    public static /*@ non_null @*/ String filterAlphabetic(/*@ non_null @*/ String string) {
        StringBuilder res = new StringBuilder();
        for (int i = 0; i < string.length(); i++) {
            char c = string.charAt(i);
            if ((c >= 'A' && c <= 'Z') || (c >= 'A' && c <= 'Z')) {
                res.append(c);
            }
        }
        return res.toString();
    }

    /**
     * Returns a Collector that accumulates the input elements into a new ImmutableList.
     *
     * @return a Collector that accumulates the input elements into a new ImmutableList.
     */
    public static <T> Collector<T, List<T>, ImmutableList<T>> collector() {
        return Collector.of(
                LinkedList::new,
                List::add,
                (list1, list2) -> {
                    list1.addAll(list2);
                    return list1;
                },
                KeYCollections::fromList);
    }

    /**
     * Creates an ImmutableList from a List.
     *
     * @param list a List.
     * @return an ImmutableList containing the same elements as the specified list.
     */
    public static <T> ImmutableList<T> fromList(List<T> list) {
        ImmutableList<T> result = nil();

        for (T el : list) {
            result = result.append(el);
        }

        return result;
    }

    /**
     * the empty list
     */
    @SuppressWarnings("unchecked")
    public static <T> ImmutableSLList<T> nil() {
        return (ImmutableSLList<T>) NIL;
    }

    public static <T> ImmutableSLList<T> singleton(T obj) {
        return new ImmutableSLList.Cons<T>(obj, nil());
    }

    public static <T> Collector<T, List<T>, ImmutableList<T>> toImmutableList() {
        return new ImmutableSLList.ImmutableListCollector<>();
    }
}
