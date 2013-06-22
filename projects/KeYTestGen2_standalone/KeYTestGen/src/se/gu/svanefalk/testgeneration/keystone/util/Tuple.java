package se.gu.svanefalk.testgeneration.keystone.util;

public class Tuple<F, S> {

    private final F first;
    private final S second;

    public Tuple(final F first, final S second) {
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
