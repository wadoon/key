package org.key_project.util.collection;

import java.lang.ref.WeakReference;
import java.util.Iterator;

import org.key_project.util.collection.TrieNode.Entry;

public class ImmutableTrieSet<T> implements ImmutableSet<T> {

    @SuppressWarnings({ "rawtypes", "unchecked" })
    private static final ImmutableTrieSet EMPTY =
            new ImmutableTrieSet(TrieNode.EMPTY, ImmutableSLList.nil());

    private static Object THING = "X";

    private final TrieNode<T, Object> map;
    private ImmutableList<WeakReference<TrieNode.Entry<T, Object>>> linearList;

    private boolean hasbeenFiltered;

    public ImmutableTrieSet(TrieNode<T, Object> map,
            ImmutableList<WeakReference<TrieNode.Entry<T, Object>>> list) {
        this.map = map;
        this.linearList = list;
        this.hasbeenFiltered = false;
    }

    @Override
    public ImmutableSet<T> add(T element) {
        Entry<T, Object> entry = map.find(element, 0);
        if(entry == null) {
            entry = new Entry<T, Object>(element, THING);
            TrieNode<T, Object> newmap = map.add(entry, 0);
            ImmutableList<WeakReference<TrieNode.Entry<T, Object>>> newlist =
                    linearList.prepend(new WeakReference<>(entry));
            return new ImmutableTrieSet<T>(newmap, newlist);
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
            ImmutableList<WeakReference<TrieNode.Entry<T, Object>>> newlist =
                    linearList.prepend(new WeakReference<>(entry));
            return new ImmutableTrieSet<T>(newmap, newlist);
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
        ImmutableSet<T> result = this;
        for (T t : set) {
            result = result.add(t);
        }
        return result;
    }

    @Override
    public Iterator<T> iterator() {
        filterList();
        return new Itr<T>(linearList);
    }

    private static final class Itr<T> implements Iterator<T> {

        private final Iterator<WeakReference<Entry<T, Object>>> it;

        public Itr(ImmutableList<WeakReference<Entry<T, Object>>> linearList) {
            it = linearList.iterator();
        }

        @Override
        public boolean hasNext() {
            return it.hasNext();
        }

        @Override
        public T next() {
            Entry<T, Object> n = it.next().get();
            assert n != null : "Filtering should have made this safe";
            return n.key();
        }

        @Override
        public void remove() {
            it.remove();
        }
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
            return new ImmutableTrieSet<T>(newmap, linearList);
        } else {
            return this;
        }
    }

    @Override
    public <S> S[] toArray(S[] array) {
        filterList();
        return linearList.toArray(array);
    }

    private void filterList() {

        if(this.hasbeenFiltered) {
            return;
        }

        if(map.size() == linearList.size()) {
            this.hasbeenFiltered = true;
            return;
        }

        ImmutableList<WeakReference<Entry<T, Object>>> result = ImmutableSLList.nil();

        WeakReference<Entry<T, Object>>[] res = (WeakReference<Entry<T, Object>>[]) new WeakReference[size()];
        int i = 0;
        ImmutableList<WeakReference<Entry<T, Object>>> rest = linearList;
        ImmutableList<WeakReference<Entry<T, Object>>> unmodifiedTail = linearList;
        WeakReference<Entry<T, Object>> t;

        TrieNode<T, Object> alreadyVisited = TrieNode.EMPTY;

        while (!rest.isEmpty()) {
            t = rest.head();
            rest = (ImmutableSLList<WeakReference<Entry<T, Object>>>) rest.tail();

            Entry<T, Object> entry = t.get();

            if (entry != null && contains(entry.key()) && alreadyVisited.find(entry.key(), 0) == null) {
                res[i++] = t;
                alreadyVisited = alreadyVisited.add(entry, 0);
            } else {
                unmodifiedTail = rest;
            }
        }

        this.linearList = ((ImmutableSLList)unmodifiedTail).prepend(res, i - unmodifiedTail.size());
        this.hasbeenFiltered = true;

        assert map.size() == linearList.size();

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
        Iterator<T> it=this.iterator();
        StringBuffer str=new StringBuffer("{");
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
