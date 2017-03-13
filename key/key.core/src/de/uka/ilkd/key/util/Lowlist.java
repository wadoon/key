package de.uka.ilkd.key.util;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.translation.SLExpression;

public class Lowlist {
    
    private final SLExpression component;
    private final IProgramMethod service;
    private final ImmutableList<Term> lowTerms;

    public Lowlist(SLExpression component, IProgramMethod service,
            ImmutableList<Term> lowTerms) {
        this.component = component;
        this.service = service;
        this.lowTerms = lowTerms;
    }

    public SLExpression getComponent() {
        return component;
    }

    public IProgramMethod getService() {
        return service;
    }

    public ImmutableList<Term> getLowTerms() {
        return lowTerms;
    }
    
    @Override
    public String toString() {
        return component.getTerm() + "." + service.getName() + lowTerms;
    }
    

}
