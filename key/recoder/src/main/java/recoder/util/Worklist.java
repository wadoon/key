package recoder.util;

import java.util.Enumeration;

public class Worklist {
    protected boolean allowDuplicates;

    protected int maxLen = 0;

    Queue impl = new Queue(HashCode.IDENTITY);

    public Worklist() {
        this(true);
    }

    public Worklist(boolean allowDuplicates) {
        this.allowDuplicates = allowDuplicates;
        this.impl.setAllowShrink(false);
    }

    public final boolean isEmpty() {
        return this.impl.isEmpty();
    }

    public void addItem(Object todo) {
        addItem(todo, this.allowDuplicates);
    }

    public void addItem(Object todo, boolean allowDuplicates) {
        if (allowDuplicates || !contains(todo)) {
            this.impl.enqueue(todo);
            int len = size();
            if (len > this.maxLen)
                this.maxLen = len;
        }
    }

    public Object getItem() {
        if (isEmpty())
            return null;
        return this.impl.first();
    }

    public Object removeItem() {
        return this.impl.dequeue();
    }

    public boolean contains(Object x) {
        return this.impl.contains(x);
    }

    public Enumeration elements() {
        return this.impl.elements();
    }

    public int size() {
        return this.impl.size();
    }

    public int getMaximumLength() {
        return this.maxLen;
    }
}
