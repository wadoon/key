package se.gu.svanefalk.keystone.util;

public class Tuple<F, S> {

    private final F first;
    private final S second;

    public Tuple(F first, S second) {
        super();
        this.first = first;
        this.second = second;
    }

    /**
     * @return the first
     */
    public F getFirst() {
        return first;
    }

    /**
     * @return the second
     */
    public S getSecond() {
        return second;
    }
}
