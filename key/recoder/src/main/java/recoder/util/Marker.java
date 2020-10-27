package recoder.util;

import java.util.HashSet;
import java.util.Set;

public class Marker implements Cloneable {
    private final Set<Object> marks = new HashSet();

    public void mark(Object o) {
        this.marks.add(o);
    }

    public void unmark(Object o) {
        this.marks.remove(o);
    }

    public boolean isMarked(Object o) {
        return this.marks.contains(o);
    }
}
