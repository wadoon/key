package de.uka.ilkd.keyabs.logic.ldt;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

public interface IHeapLDT {

    /**
     * Returns the sort "Field".
     */
    public abstract Sort getFieldSort();

    /**
     * Returns the select function for the given sort.
     */
    public abstract Function getSelect(Sort instanceSort, IServices services);

    /**
     * If the passed operator is an instance of "select", this method returns
     * the sort of the function (identical to its return type); otherwise, 
     * returns null.
     */
    public abstract Sort getSortOfSelect(Operator op);

    public abstract Function getStore();

    public abstract Function getReach();

    public abstract Function getAcc();

    public abstract Function getAnon();
    
    public abstract Function getNull();

    public abstract LocationVariable getHeap();

    public abstract ImmutableArray<LocationVariable> getAllHeaps();

    public abstract String getPrettyFieldName(Named op);

    Function getFieldSymbolForPV(LocationVariable fieldPV, IServices services);
}