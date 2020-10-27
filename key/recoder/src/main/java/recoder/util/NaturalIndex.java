package recoder.util;

public class NaturalIndex extends AbstractIndex {
    public NaturalIndex() {
    }

    public NaturalIndex(int initialCapacity) {
        super(initialCapacity);
    }

    public final int hashCode(Object o) {
        return o.hashCode();
    }

    public final boolean equals(Object p, Object q) {
        return p.equals(q);
    }
}
