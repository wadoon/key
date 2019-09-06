package de.uka.ilkd.key.strategy.conflictbasedinst;

public class CbiPair {

    private ConstrainedAssignment ca;
    private MatchingConstraints mc;

    public CbiPair(ConstrainedAssignment ca, MatchingConstraints mc) {
        this.ca = ca;
        this.mc = mc;
    }

    public ConstrainedAssignment getConstrainedAssignment() {
        return ca;
    }

    public MatchingConstraints getMatchingConstraints() {
        return mc;
    }

    @Override
    public String toString() {
        return "(" + ca.toString() + ", " + mc.toString() + ")";
    }



}
