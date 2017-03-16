package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.util.DependencyClusterSpec;

public interface DependencyClusterContract extends Contract {
    public IProgramMethod getTarget();
    
    public Modality getModality();

    public KeYJavaType getSpecifiedIn();

    public Term getPre();

    public Term getMod();

    public boolean hasModifiesClause();

    public Term getSelfVar();

    public ImmutableList<Term> getParams();

    public Term getResult();

    public Term getExc();

    public Term getDep();

    public Term getHeapAtPre();

    public ImmutableList<DependencyClusterSpec> getSpecs();
}
