package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RewriteTaclet;

public abstract class AbstractDependencyClusterSpec
        implements DependencyClusterSpec {
     
    protected final String label;
    protected final Services services;
    
    private final Function equivEventEqPredicate;
    private final Function equivEventIsoPredicate;
    private final Function agreePrePredicate;
    private final Function invisPredicate;
    
    public AbstractDependencyClusterSpec(String label, Services services) {
        this.label = label;
        this.services = services;
        
        Sort eventSort = services.getTypeConverter().getRemoteMethodEventLDT().eventSort();
        Sort formulaSort = services.getTermBuilder().tt().sort();
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        equivEventEqPredicate = new Function(new Name("EquivEventEq_" + label), formulaSort, eventSort, eventSort);
        equivEventIsoPredicate = new Function(new Name("EquivEventIso_" + label), formulaSort, eventSort, eventSort);
        agreePrePredicate = new Function(new Name("AgreePre_" + label), formulaSort, heapSort, heapSort);
        invisPredicate = new Function(new Name("InvisEvent_" + label), formulaSort, eventSort);
    }


    @Override
    public Function getAgreePrePredicate() {
        return agreePrePredicate;
    }


    @Override
    public Function getVisibilityPredicate() {
        return invisPredicate;
    }



    @Override
    public Function getEquivEventEqPredicate() {
        return equivEventEqPredicate;
    }



    @Override
    public Function getEquivEventIsoPredicate() {
        return equivEventIsoPredicate;
    }
    
    //TODO JK apparently registering isn't necessary... maybe you only need if you wan't to do lookups later... Still, better double check what difference this would make
    @Override
    public void registerPredicates() {
        services.getNamespaces().functions().addSafely(agreePrePredicate);
        services.getNamespaces().functions().addSafely(equivEventEqPredicate);
        services.getNamespaces().functions().addSafely(equivEventIsoPredicate);
        services.getNamespaces().functions().addSafely(invisPredicate);
    }
    
}
