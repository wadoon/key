package recoder.util;

import java.util.Enumeration;
import java.util.NoSuchElementException;

public abstract class AbstractIndex implements HashCode {
    private static final float THRESHOLD = 0.75F;
    private static final Object DELETED = new Object() {
        public boolean equals(Object x) {
            return false;
        }

        public String toString() {
            return "<DELETED>";
        }
    };
    Object[] table;
    long[] id;
    int count;
    int ld;

    public AbstractIndex() {
        this(4);
    }

    public AbstractIndex(int initialCapacity) {
        if (initialCapacity < 4)
            initialCapacity = 4;
        int cap = 4;
        this.ld = 2;
        while (cap < initialCapacity) {
            this.ld++;
            cap += cap;
        }
        this.table = new Object[cap];
        this.id = new long[cap];
        this.ld = 32 - this.ld;
    }

    public final int size() {
        return this.count;
    }

    public final boolean isEmpty() {
        return (size() == 0);
    }

    private void rehash() {
        Object[] oldMap = this.table;
        long[] oldId = this.id;
        int oldCapacity = oldMap.length;
        this.ld--;
        this.table = new Object[oldCapacity * 2];
        this.id = new long[oldCapacity * 2];
        this.count = 0;
        for (int i = oldCapacity - 1; i >= 0; i--) {
            Object ob = oldMap[i];
            if (ob != null && ob != DELETED)
                insert(ob, oldId[i]);
        }
    }

    public boolean contains(Object key) {
        if (key == null)
            return false;
        int hash = -1640531527 * hashCode(key) >>> this.ld;
        int index = hash;
        while (true) {
            Object ob = this.table[index];
            if (ob == null)
                return false;
            if (equals(ob, key))
                return true;
            index = index + (hash | 0x1) & this.table.length - 1;
            if (index == hash)
                return false;
        }
    }

    public final long get(Object key) {
        if (key == null)
            return -1L;
        int hash = -1640531527 * hashCode(key) >>> this.ld;
        int index = hash;
        while (true) {
            Object ob = this.table[index];
            if (ob == null)
                return -1L;
            if (equals(ob, key))
                return this.id[index];
            index = index + (hash | 0x1) & this.table.length - 1;
            if (index == hash)
                return -1L;
        }
    }

    public final long put(Object key, long id) {
        if (key == null)
            throw new IllegalArgumentException("Null key");
        if (this.count >= this.table.length * 0.75F)
            rehash();
        return insert(key, id);
    }

    private long insert(Object key, long id) {
        int hash = -1640531527 * hashCode(key) >>> this.ld;
        int index = hash;
        do {
            Object ob = this.table[index];
            if (ob == null || ob == DELETED) {
                this.table[index] = key;
                this.id[index] = id;
                this.count++;
                return -1L;
            }
            if (equals(ob, key)) {
                long i = this.id[index];
                this.table[index] = key;
                this.id[index] = id;
                return i;
            }
            index = index + (hash | 0x1) & this.table.length - 1;
        } while (index != hash);
        rehash();
        return insert(key, id);
    }

    public final long remove(Object key) {
        if (key == null)
            throw new IllegalArgumentException("Null key");
        int hash = -1640531527 * hashCode(key) >>> this.ld;
        int index = hash;
        while (true) {
            Object ob = this.table[index];
            if (ob == null)
                return -1L;
            if (equals(ob, key)) {
                this.table[index] = DELETED;
                this.count--;
                return this.id[index];
            }
            index = index + (hash | 0x1) & this.table.length - 1;
            if (index == hash)
                return -1L;
        }
    }

    public void clear() {
        for (int index = this.table.length; --index >= 0; this.table[index] = null) ;
        this.count = 0;
    }

    public final Enumeration elements() {
        return new Enumerator(this.table);
    }

    public boolean equals(Object ob) {
        if (!(ob instanceof AbstractIndex))
            return false;
        AbstractIndex x = (AbstractIndex) ob;
        if (x.size() != size())
            return false;
        Enumeration enum2 = x.elements();
        while (enum2.hasMoreElements()) {
            Object z = enum2.nextElement();
            if (get(z) != x.get(z))
                return false;
        }
        return true;
    }

    public Object clone() {
        try {
            AbstractIndex t = (AbstractIndex) super.clone();
            t.table = new Object[this.table.length];
            for (int i = this.table.length; i-- > 0; ) {
                t.table[i] = this.table[i];
                t.id[i] = this.id[i];
            }
            return t;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }

    public String toString() {
        int max = size() - 1;
        StringBuffer buf = new StringBuffer();
        Enumeration<E> e = elements();
        buf.append("{");
        for (int i = 0; i <= max; i++) {
            String s = e.nextElement().toString();
            buf.append(s);
            buf.append("=");
            buf.append(get(s));
            if (i < max)
                buf.append(", ");
        }
        buf.append("}");
        return buf.toString();
    }

    public abstract boolean equals(Object paramObject1, Object paramObject2);

    public abstract int hashCode(Object paramObject);

    static class Enumerator implements Enumeration {
        int index;

        Object[] table;

        Enumerator(Object[] table) {
            this.table = table;
            this.index = 0;
        }

        public boolean hasMoreElements() {
            while (this.index < this.table.length) {
                if (this.table[this.index] != null && this.table[this.index] != AbstractIndex.DELETED)
                    return true;
                this.index++;
            }
            return false;
        }

        public Object nextElement() {
            while (this.index < this.table.length) {
                if (this.table[this.index] != null && this.table[this.index] != AbstractIndex.DELETED)
                    return this.table[this.index++];
                this.index++;
            }
            throw new NoSuchElementException("Enumerator");
        }
    }
}
