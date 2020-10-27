package recoder.util;

import java.util.Enumeration;
import java.util.NoSuchElementException;

public class Index implements Cloneable {
    private final HashCode hasher;
    private transient Entry[] table;
    private transient int count;
    private transient int ld;

    public Index() {
        this(null, 8);
    }

    public Index(HashCode hasher) {
        this(hasher, 8);
    }

    public Index(int initialCapacity) {
        this(null, initialCapacity);
    }

    public Index(HashCode hasher, int initialCapacity) {
        this.hasher = (hasher != null) ? hasher : HashCode.NATURAL;
        if (initialCapacity < 4)
            initialCapacity = 4;
        this.ld = 2;
        int cap = 4;
        while (cap < initialCapacity) {
            this.ld++;
            cap += cap;
        }
        this.table = new Entry[cap];
        this.ld = 32 - this.ld;
    }

    public int size() {
        return this.count;
    }

    public boolean isEmpty() {
        return (this.count == 0);
    }

    public Enumeration keys() {
        return new Enumerator(this.table);
    }

    final void rehash() {
        Entry[] oldMap = this.table;
        int oldCapacity = oldMap.length;
        int newCapacity = oldCapacity * 2;
        this.ld--;
        Entry[] newMap = this.table = new Entry[newCapacity];
        for (int i = oldCapacity; i-- > 0; ) {
            Entry e = oldMap[i];
            while (e != null) {
                int index = -1640531527 * e.hash >>> this.ld;
                Entry f = e.next;
                e.next = newMap[index];
                newMap[index] = e;
                e = f;
            }
        }
    }

    public boolean contains(long value) {
        Entry[] tab = this.table;
        for (int i = tab.length; i-- > 0; ) {
            for (Entry e = tab[i]; e != null; e = e.next) {
                if (e.value == value)
                    return true;
            }
        }
        return false;
    }

    public boolean containsKey(Object key) {
        int hash = this.hasher.hashCode(key);
        int index = -1640531527 * hash >>> this.ld;
        for (Entry e = this.table[index]; e != null; e = e.next) {
            if (e.hash == hash && this.hasher.equals(e.key, key))
                return true;
        }
        return false;
    }

    public long get(Object key) {
        int hash = this.hasher.hashCode(key);
        int index = -1640531527 * hash >>> this.ld;
        for (Entry e = this.table[index]; e != null; e = e.next) {
            if (e.hash == hash && this.hasher.equals(e.key, key))
                return e.value;
        }
        return -1L;
    }

    public long put(Object key, long value) {
        Debug.assertBoolean((value >= 0L));
        int hash = this.hasher.hashCode(key);
        int index = -1640531527 * hash >>> this.ld;
        for (Entry e = this.table[index]; e != null; e = e.next) {
            if (e.hash == hash && this.hasher.equals(e.key, key)) {
                long old = e.value;
                e.value = value;
                return old;
            }
        }
        if (this.count >= this.table.length) {
            rehash();
            return put(key, value);
        }
        this.table[index] = new Entry(hash, key, value, this.table[index]);
        this.count++;
        return -1L;
    }

    public long remove(Object key) {
        int hash = this.hasher.hashCode(key);
        int index = -1640531527 * hash >>> this.ld;
        for (Entry e = this.table[index], d = null; e != null; d = e, e = e.next) {
            if (e.hash == hash && this.hasher.equals(e.key, key)) {
                if (d != null) {
                    d.next = e.next;
                } else {
                    this.table[index] = e.next;
                }
                this.count--;
                return e.value;
            }
        }
        return -1L;
    }

    public void clear() {
        Entry[] tab = this.table;
        for (int index = tab.length; --index >= 0; )
            tab[index] = null;
        this.count = 0;
    }

    public Object clone() {
        try {
            Index t = (Index) super.clone();
            t.table = new Entry[this.table.length];
            for (int i = this.table.length; i-- > 0; )
                t.table[i] = (this.table[i] != null) ? (Entry) this.table[i].clone() : null;
            return t;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }

    public String toString() {
        int max = size() - 1;
        StringBuffer buf = new StringBuffer();
        Enumeration k = keys();
        buf.append("{");
        for (int i = 0; i <= max; i++) {
            Object key = k.nextElement();
            buf.append(key.toString() + "=" + get(key));
            if (i < max)
                buf.append(", ");
        }
        buf.append("}");
        return buf.toString();
    }

    static class Entry {
        int hash;

        Object key;

        long value;

        Entry next;

        public Entry(int hash, Object key, long value, Entry next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        protected Object clone() {
            return new Entry(this.hash, this.key, this.value, (this.next != null) ? (Entry) this.next.clone() : null);
        }
    }

    private static class Enumerator implements Enumeration {
        int index;

        Index.Entry[] table;

        Index.Entry entry;

        Enumerator(Index.Entry[] table) {
            this.table = table;
            this.index = table.length;
        }

        public boolean hasMoreElements() {
            if (this.entry != null)
                return true;
            while (this.index-- > 0) {
                if ((this.entry = this.table[this.index]) != null)
                    return true;
            }
            return false;
        }

        public Object nextElement() {
            if (this.entry == null)
                while (this.index-- > 0 && (this.entry = this.table[this.index]) == null) ;
            if (this.entry != null) {
                Index.Entry e = this.entry;
                this.entry = e.next;
                return e.key;
            }
            throw new NoSuchElementException("Enumerator");
        }
    }
}
