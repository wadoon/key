package de.uka.ilkd.key.logic.op;

import org.key_project.common.core.logic.op.DLSortedOperator;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public interface SortedOperator extends DLSortedOperator<Sort, Term>, Operator {

    
    public ImmutableArray<Sort> argSorts();

}
