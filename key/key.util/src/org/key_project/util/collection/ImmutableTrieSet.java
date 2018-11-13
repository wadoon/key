package org.key_project.util.collection;

import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.lang.reflect.Array;
import java.util.Iterator;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.TrieNode.Entry;

public class ImmutableTrieSet<T> implements ImmutableSet<T> {

    @SuppressWarnings({ "rawtypes", "unchecked" })
    private static final ImmutableTrieSet EMPTY =
            new ImmutableTrieSet(TrieNode.EMPTY);

    private static Object THING = "X";

    private final TrieNode<T, Object> map;

    public ImmutableTrieSet(TrieNode<T, Object> map) {
        this.map = map;
    }

    @Override
    public ImmutableSet<T> add(T element) {
        Entry<T, Object> entry = map.find(element, 0);
        if(entry == null) {
            entry = new Entry<T, Object>(element, THING);
            TrieNode<T, Object> newmap = map.add(entry, 0);
            return new ImmutableTrieSet<T>(newmap);
        } else {
            return this;
        }
    }

    @Override
    public ImmutableSet<T> addUnique(T element) throws NotUniqueException {
        Entry<T, Object> entry = map.find(element, 0);
        if(entry == null) {
            entry = new Entry<T, Object>(element, THING);
            TrieNode<T, Object> newmap = map.add(entry, 0);
            return new ImmutableTrieSet<T>(newmap);
        } else {
            throw new NotUniqueException(element);
        }
    }

    @Override
    public ImmutableSet<T> union(ImmutableSet<T> set) {
        ImmutableSet<T> result = this;
        for (T t : set) {
            result = result.add(t);
        }
        return result;
    }

    @Override
    public ImmutableSet<T> intersect(ImmutableSet<T> set) {
        ImmutableSet<T> result = DefaultImmutableSet.nil();
        for (T t : this) {
            if(set.contains(t)) {
                result = result.add(t);
            }
        }
        return result;
    }

    @Override
    public Iterator<T> iterator() {
        return new MappedIterator<Entry<T,Object>, T>(map.iterator(),  x -> x.key());
    }

    @Override
    public Stream<T> stream() {
        return StreamSupport.stream(spliterator(), false);
    }

    @Override
    public boolean contains(T obj) {
        return map.find(obj, 0) != null;
    }

    @Override
    public boolean subset(ImmutableSet<T> s) {
        for (T t : this) {
            if(!s.contains(t)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public int size() {
        return map.size();
    }

    @Override
    public boolean isEmpty() {
        return size() == 0;
    }

    @Override
    public ImmutableSet<T> remove(T element) {
        if(contains(element)) {
            TrieNode<T, Object> newmap = map.remove(element, 0);
            return new ImmutableTrieSet<T>(newmap);
        } else {
            return this;
        }
    }

    @Override
    public <S> S[] toArray(S[] array) {
        if(size() > array.length) {
            array = (S[]) Array.newInstance(array.getClass().getComponentType(), size());
        }

        int i = 0;
        for (T t : this) {
            array[i++] = (S)t;
        }

        return array;
    }

    @SuppressWarnings("unchecked")
    public static <T> ImmutableTrieSet<T> empty() {
        return (ImmutableTrieSet<T>)EMPTY;
    }

    @Override
    public int hashCode() {
        return map.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj==this) {
            return true;
        }

        if (!(obj instanceof ImmutableSet)) {
            return false;
        }

        @SuppressWarnings("unchecked")
        ImmutableSet<T> o=(ImmutableSet<T>) obj;

        return (o.subset(this) && this.subset(o));
    }

    @Override
    public String toString() {
        Iterator<T> it = this.iterator();
        StringBuffer str = new StringBuffer("{");
        while (it.hasNext()) {
            str.append(it.next());
            if (it.hasNext()) {
                str.append(",");
            }
        }
        str.append("}");
        return str.toString();
    }

}
