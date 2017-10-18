package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.util.Lowlist;
import de.uka.ilkd.key.util.VisibilityCondition;

public interface ComponentCluster extends SpecificationElement, DependencyClusterSpec  {
    public ImmutableList<Lowlist> getLowOut();

    public ImmutableList<Lowlist> getLowIn();
    

    public ImmutableList<Term> getLowState();

    public ImmutableList<VisibilityCondition> getVisible();
    
    public String getLabel();

}
