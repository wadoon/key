package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;

public class CombinedClusterSpec extends AbstractDependencyClusterSpec {
    
    private final ImmutableList<String> specLabels;

    public CombinedClusterSpec(String label, Services services, ImmutableList<String> specLabels) {
        super(label, services);
        this.specLabels = specLabels;
    }

    public ImmutableList<String> getSpecLabels() {
        return specLabels;
    }
    
    @Override
    public String toString() {
        return "cluster " + label + " combines " + specLabels;
    }
}
