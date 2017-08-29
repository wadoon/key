package de.uka.ilkd.key.util;

public class ClusterSatisfactionSpec {
    private final String componentClusterLabel;
    private final String serviceClusterLabel;
    
    public ClusterSatisfactionSpec(String componentClusterLabel, String serviceClusterLabel) {
        this.componentClusterLabel = componentClusterLabel;
        this.serviceClusterLabel = serviceClusterLabel;
    }

    public String getComponentClusterLabel() {
        return componentClusterLabel;
    }

    public String getServiceClusterLabel() {
        return serviceClusterLabel;
    }
    
    @Override
    public String toString() {
        return  componentClusterLabel + " satisfied by " + serviceClusterLabel;
    }
}
