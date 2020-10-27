package recoder.util;

import java.util.Enumeration;
import java.util.NoSuchElementException;

public class Queue {
    private static final int DEFAULT_INITIAL_CAPACITY = 32;

    private static final Equality DEFAULT_EQUALITY = HashCode.NATURAL;

    protected Equality equality;

    protected Object[] data;

    protected boolean allowShrink = true;

    protected int start;

    protected int end;

    public Queue() {
        this(32, DEFAULT_EQUALITY);
    }

    public Queue(int initialCapacity) {
        this(initialCapacity, DEFAULT_EQUALITY);
    }

    public Queue(Equality equality) {
        this(32, equality);
    }

    public Queue(int initialCapacity, Equality equality) {
        this.data = new Object[initialCapacity];
        this.equality = equality;
        this.start = -1;
        this.end = -1;
    }

    public int capacity() {
        return this.data.length;
    }

    public int size() {
        if (this.start == -1)
            return 0;
        if (this.start > this.end)
            return this.data.length - this.start - this.end + 1;
        return this.end - this.start + 1;
    }

    private void copyArray(Object[] dest) {
        int size = size();
        if (size > 0)
            if (this.start <= this.end) {
                System.arraycopy(this.data, this.start, dest, 0, size);
            } else {
                int l1 = this.data.length - this.start;
                System.arraycopy(this.data, this.start, dest, 0, l1);
                System.arraycopy(this.data, 0, dest, l1, this.end + 1);
            }
    }

    private void grow() {
        int newSize = this.data.length * 2;
        if (newSize == 0)
            newSize = 1;
        Object[] newData = new Object[newSize];
        if (this.start != -1) {
            copyArray(newData);
            this.end = size() - 1;
            this.start = 0;
        }
        this.data = newData;
    }

    public void setAllowShrink(boolean allow) {
        this.allowShrink = allow;
    }

    private void shrink() {
        if (this.data.length > 31) {
            Object[] newData = new Object[this.data.length / 2];
            if (this.start != -1) {
                copyArray(newData);
                this.end = size() - 1;
                this.start = 0;
            }
            this.data = newData;
        }
    }

    public final boolean isEmpty() {
        return (this.start == -1);
    }

    public void enqueue(Object x) {
        if (size() == this.data.length)
            grow();
        if (isEmpty()) {
            this.start = 0;
            this.end = 0;
            this.data[0] = x;
        } else if (this.end < this.data.length - 1) {
            this.data[++this.end] = x;
        } else {
            this.end = 0;
            this.data[0] = x;
        }
    }

    public Object dequeue() {
        if (isEmpty())
            return null;
        Object result = this.data[this.start];
        if (this.start == this.end) {
            this.start = -1;
            this.end = -1;
        } else if (this.start < this.data.length - 1) {
            this.start++;
        } else {
            this.start = 0;
        }
        if (this.allowShrink && size() < this.data.length / 3)
            shrink();
        return result;
    }

    public Object first() {
        if (this.start != -1)
            return this.data[this.start];
        return null;
    }

    public boolean contains(Object x) {
        if (isEmpty() || x == null)
            return false;
        boolean result = false;
        if (this.start <= this.end) {
            for (int i = this.start; i <= this.end && !result; i++)
                result = this.equality.equals(this.data[i], x);
        } else {
            int i;
            for (i = this.start; i < this.data.length && !result; i++)
                result = this.equality.equals(this.data[i], x);
            for (i = 0; i <= this.end && !result; i++)
                result = this.equality.equals(this.data[i], x);
        }
        return result;
    }

    public Enumeration elements() {
        return new QueueEnumeration();
    }

    protected class QueueEnumeration implements Enumeration {
        int currPos = Queue.this.start;

        boolean more = (Queue.this.start != -1);

        public boolean hasMoreElements() {
            return this.more;
        }

        public Object nextElement() throws NoSuchElementException {
            if (!this.more)
                throw new NoSuchElementException();
            Object result = Queue.this.data[this.currPos];
            if (this.currPos == Queue.this.end) {
                this.more = false;
            } else {
                this.currPos++;
                if (this.currPos == Queue.this.data.length)
                    this.currPos = 0;
            }
            return result;
        }
    }
}
