package org.key_project.util.collection;

import java.util.Iterator;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

class SharedSet<T> {

    private static class Entry {
        final Tag tag;
        final Entry next;
        final boolean isRemoveTag;

        public Entry(Tag tag, Entry entry, boolean isRemove) {
            this.tag = tag;
            this.next = entry;
            this.isRemoveTag = isRemove;
        }

        public static Entry addEntry(Tag tag, Entry entry) {
            return new Entry(tag, entry, false);
        }

        public static Entry removeEntry(Tag tag, Entry entry) {
            return new Entry(tag, entry, true);
        }
    }

    private final ConcurrentHashMap<T, Entry> map;
    private final AtomicInteger modCount = new AtomicInteger(0);

    public SharedSet(Iterable<T> history) {
        this.map = new ConcurrentHashMap<T, Entry>(16, .75f, 4);
        for (T hist : history) {
            addNoIncrement(hist, Tag.INIT);
        }
    }

    public boolean add(T element, Tag tag) {
        boolean res = addNoIncrement(element, tag);
        if(res) {
            modCount.incrementAndGet();
        }
        return res;
    }

    public boolean addNoIncrement(T element, Tag tag) {
        Entry entry = map.get(element);
        if(contains(tag, entry)) {
            return false;
        }

        boolean ok;
        do {
            entry = map.get(element);
            ok = map.replace(element, entry, Entry.addEntry(tag, entry));
        } while(!ok);

        modCount.incrementAndGet();
        return true;
    }

    public boolean remove(T element, Tag tag) {
        Entry entry = map.get(element);
        if(!contains(tag, entry)) {
            return false;
        }

        boolean ok;
        do {
            entry = map.get(element);
            ok = map.replace(element, entry, Entry.removeEntry(tag, entry));
        } while(!ok);

        return true;
    }

    public boolean contains(T element, Tag tag) {
        Entry entry = map.get(element);
        return contains(tag, entry);
    }

    private boolean contains(Tag tag, Entry entry) {
        while(entry != null) {
            if(entry.tag.isPrefixOf(tag)) {
                return !entry.isRemoveTag;
            }
            entry = entry.next;
        }
        return false;
    }

    public int getModCount() {
        return modCount.get();
    }

}

class Tag {

    public final static Tag INIT = new Tag(0, null);

    public final int id;
    public final Tag parent;

    public Tag(int id, Tag parent) {
        this.id = id;
        this.parent = parent;
    }

    public boolean isPrefixOf(Tag tag) {
        Tag p = this;
        while(p != null) {
            // tag ends before prefix: false
            // different ids: false
            if(tag == null || tag.id != p.id) {
                return false;
            }
            tag = tag.parent;
            p = p.parent;
        }
        return true;
    }
}

public class ImmutableSharedHashSet<T> implements ImmutableSet<T> {

    private static final long serialVersionUID = 6725296130973289597L;

    private final SharedSet<T> sharedSet;
    private ImmutableList<T> elementList;
    private final Tag tag;
    private final AtomicInteger tagIdCounter = new AtomicInteger(0);


    private ImmutableSharedHashSet(ImmutableList<T> history) {
        this.tag = Tag.INIT;
        this.elementList = history;
        this.sharedSet = new SharedSet<>(history);
    }

    private ImmutableSharedHashSet(ImmutableSharedHashSet<T> orig) {
        SharedSet<T> set = orig.sharedSet;
        if(set.getModCount() > 1000) {
            this.tag = Tag.INIT;
            this.elementList = orig.elementList;
            this.sharedSet = new SharedSet<>(orig.elementList);
        } else {
            this.tag = orig.newChildTag();
            this.sharedSet = set;
            this.elementList = orig.elementList;
        }

    }

    private Tag newChildTag() {
        return new Tag(tagIdCounter.incrementAndGet(), tag);
    }

    @Override
    public ImmutableSet<T> add(T element) {
        if(contains(element)) {
            return this;
        } else {
            ImmutableSharedHashSet<T> result = new ImmutableSharedHashSet<>(this);
            result.sharedSet.add(element, result.tag);
            result.elementList = elementList.prepend(element);
            return result;
        }
    }

    @Override
    public ImmutableSet<T> union(ImmutableSet<T> set) {
        ImmutableSharedHashSet<T> result = new ImmutableSharedHashSet<>(this);
        for (T element : set) {
            if(result.sharedSet.add(element, result.tag)) {
                result.elementList = elementList.prepend(element);
            }
        }

        if(result.size() > this.size()) {
            return result;
        } else {
            return this;
        }
    }

    @Override
    public ImmutableSet<T> intersect(ImmutableSet<T> set) {
        if (set.isEmpty()) {
            return set;
        }

        // from DefaultImmutableSet:
        ImmutableList<T> intersectElements = this.elementList;
        for (T el : intersectElements) {
            if (!set.contains(el)) {
                intersectElements = intersectElements.removeFirst(el);
            }
        }

        return new ImmutableSharedHashSet<T>(intersectElements);
    }

    @Override
    public Iterator<T> iterator() {
        return elementList.iterator();
    }

    @Override
    public boolean contains(T obj) {
        return sharedSet.contains(obj, tag);
    }

    @Override
    public boolean subset(ImmutableSet<T> set) {
        for (T element : set) {
            if(!contains(element)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public int size() {
        return elementList.size();
    }

    @Override
    public boolean isEmpty() {
        return elementList.isEmpty();
    }

    @Override
    public ImmutableSet<T> remove(T element) {
        if(contains(element)) {
            ImmutableSharedHashSet<T> result = new ImmutableSharedHashSet<>(this);
            result.sharedSet.remove(element, result.tag);
            result.elementList = elementList.removeFirst(element);
            return result;
        } else {
            return this;
        }
    }

    @Override
    public ImmutableSet<T> addUnique(T element) throws NotUniqueException {
        if(contains(element)) {
            throw new NotUniqueException(element);
        }
        return add(element);
    }

    @Override
    public <S> S[] toArray(S[] array) {
        return elementList.toArray(array);
    }

    /**
     * Get the underlying immutable list.
     *
     * @return an immutable list with the same iteration order as this set.
     */
    public ImmutableList<T> toImmutableList() {
        return elementList;
    }

    /**
     * Create an immutable set from an immutable list.
     *
     * @param list
     *            a non-null immutable list
     * @return a fresh immutable set with the same iteration order.
     */
    public static<T> ImmutableSet<T> fromImmutableList(ImmutableList<T> list) {
        return new ImmutableSharedHashSet<T>(list);
    }

    /**
     * Create an immutable set from an immutable list.
     *
     * @param list
     *            a non-null immutable list
     * @return a fresh immutable set with the same iteration order.
     */
    public static<T> ImmutableSet<T> from(Iterable<T> list) {
        ImmutableList<T> result = ImmutableSLList.<T>nil();
        result = result.prepend(list);
        return new ImmutableSharedHashSet<T>(result);
    }

    @Override
    public Stream<T> stream() {
        return StreamSupport.stream(spliterator(), false);
    }

}
