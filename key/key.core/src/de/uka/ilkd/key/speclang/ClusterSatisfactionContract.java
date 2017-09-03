package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.util.ClusterSatisfactionSpec;

public interface ClusterSatisfactionContract extends Contract {
    public ClusterSatisfactionSpec getSpecs();
   
    public IProgramMethod getTarget();
    
    public Term getMod();
}
