package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.RewriteTaclet;

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

    @Override
    public ImmutableList<RewriteTaclet> getTaclets(Term self,
            InitConfig config) {
        // TODO Auto-generated method stub
        return null;
    }

}
