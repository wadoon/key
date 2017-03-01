package de.uka.ilkd.key.util;

public class DependencyClusterSpec {
    public static final DependencyClusterSpec EMPTY_DEP_CLUSTER_SPEC = new DependencyClusterSpec("");
    
    //TODO build class
    //private final ImmutableList<Term> lowIn; ...
    private String text;

    public DependencyClusterSpec(String text) {
        this.text = text;
    }
    
    @Override
    public String toString() {
        return text;    
    }
}
