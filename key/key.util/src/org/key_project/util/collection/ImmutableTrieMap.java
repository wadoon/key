package org.key_project.util.collection;

import java.lang.ref.WeakReference;
import java.util.Iterator;

import org.key_project.util.collection.TrieNode.Entry;

public class ImmutableTrieMap<S, T> implements ImmutableMap<S, T> {

    private static final ImmutableTrieMap EMPTY =
            new ImmutableTrieMap(TrieNode.EMPTY, ImmutableSLList.nil());

    private final TrieNode<S, T> root;
    private ImmutableList<WeakReference<TrieNode.Entry<S,T>>> linearList;
    private boolean hasbeenFiltered;

    private ImmutableTrieMap(TrieNode<S, T> root,
            ImmutableList<WeakReference<Entry<S, T>>> linearList) {
        this.root = root;
        this.linearList = linearList;
    }

    @Override
    public ImmutableMap<S, T> put(S key, T value) {
        Entry<S, T> entry = new Entry<S,T>(key, value);
        TrieNode<S, T> newroot = root.add(entry, 0);
        return new ImmutableTrieMap<S,T>(newroot, linearList.prepend(new WeakReference<>(entry)));
    }

    @Override
    public T get(S key) {
        Entry<S, T> entry = root.find(key, 0);
        if(entry != null) {
            return entry.value();
        } else {
            return null;
        }
    }

    @Override
    public int size() {
        return root.size();
    }

    @Override
    public boolean isEmpty() {
        return size() == 0;
    }

    @Override
    public boolean containsKey(S key) {
        Entry<S, T> entry = root.find(key, 0);
        return entry != null;
    }

    @Override
    public boolean containsValue(T value) {
        Iterator<T> it = valueIterator();
        while(it.hasNext()) {
            if(it.next().equals(value)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public ImmutableMap<S, T> remove(S key) {
        TrieNode<S, T> newroot = root.remove(key, 0);
        if(root == newroot) {
            return this;
        } else {
            return new ImmutableTrieMap<>(newroot, linearList);
        }
    }

    @Override
    public ImmutableMap<S, T> removeAll(T value) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Iterator<S> keyIterator() {
        final Iterator<WeakReference<Entry<S, T>>> it = entryIterator();
        return new Iterator<S>() {

            @Override
            public boolean hasNext() {
                return it.hasNext();
            }

            @Override
            public S next() {
                return it.next().get().key();
            }

            @Override
            public void remove() {
                it.remove();
            }

        };
    }

    @Override
    public Iterator<T> valueIterator() {
        final Iterator<WeakReference<Entry<S, T>>> it = entryIterator();
        return new Iterator<T>() {

            @Override
            public boolean hasNext() {
                return it.hasNext();
            }

            @Override
            public T next() {
                return it.next().get().value();
            }

            @Override
            public void remove() {
                it.remove();
            }

        };

    }

    @Override
    public Iterator<ImmutableMapEntry<S, T>> iterator() {
        final Iterator<WeakReference<Entry<S, T>>> it = entryIterator();
        return new Iterator<ImmutableMapEntry<S, T>>() {

            @Override
            public boolean hasNext() {
                return it.hasNext();
            }

            @Override
            public ImmutableMapEntry<S, T> next() {
                return it.next().get();
            }

            @Override
            public void remove() {
                it.remove();
            }

        };
    }

    private Iterator<WeakReference<Entry<S, T>>> entryIterator() {
        filterList();
        return linearList.iterator();
    }

    private void filterList() {

        if(this.hasbeenFiltered) {
            return;
        }

        ImmutableList<WeakReference<Entry<S, T>>> result = ImmutableSLList.nil();

        WeakReference<Entry<S, T>>[] res = (WeakReference<Entry<S, T>>[]) new WeakReference[size()];
        int i = 0;
        ImmutableList<WeakReference<Entry<S, T>>> rest = linearList;
        ImmutableList<WeakReference<Entry<S, T>>> unmodifiedTail = linearList;
        WeakReference<Entry<S, T>> t;

        TrieNode<S, T> alreadyVisited = TrieNode.EMPTY;

        while (!rest.isEmpty()) {
            t = rest.head();
            rest = (ImmutableSLList<WeakReference<Entry<S,T>>>) rest.tail();

            Entry<S,T> entry = t.get();

            if (entry != null && containsKey(entry.key()) && alreadyVisited.find(entry.key(), 0) == null) {
                res[i++] = t;
                alreadyVisited = alreadyVisited.add(entry, 0);
            } else {
                unmodifiedTail = rest;
            }
        }

        this.linearList = ((ImmutableSLList)unmodifiedTail).prepend(res, i - unmodifiedTail.size());
        this.hasbeenFiltered = true;
    }

    public static <S,T> ImmutableTrieMap<S, T> empty() {
        return (ImmutableTrieMap<S, T>)EMPTY;
    }



}
