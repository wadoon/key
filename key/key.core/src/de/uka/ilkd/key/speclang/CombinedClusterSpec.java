package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;

public class CombinedClusterSpec extends AbstractDependencyClusterSpec {
    
    private final ImmutableList<DependencyClusterSpec> specs;

    public CombinedClusterSpec(String label, Services services, ImmutableList<DependencyClusterSpec> specs) {
        super(label, services);
        this.specs = specs;
    }

}
