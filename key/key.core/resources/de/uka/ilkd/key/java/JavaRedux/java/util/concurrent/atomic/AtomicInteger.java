package java.util.concurrent.atomic.AtomicInteger;

public class AtomicInteger extends Number implements java.io.Serializable {

    private int value;


    public /*@ strictly_pure @*/ final int get() {
        return value;
    }

    // contract will be hard-coded
    public final boolean compareAndSet(int expect, int update);
}
