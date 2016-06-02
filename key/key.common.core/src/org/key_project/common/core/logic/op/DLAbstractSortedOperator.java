package org.key_project.common.core.logic.op;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Sort ;
import org.key_project.util.collection.ImmutableArray;

public abstract class DLAbstractSortedOperator
extends DLAbstractOperator implements SortedOperator {

    protected static final ImmutableArray<Sort> EMPTY_SORT_LIST = new ImmutableArray<Sort>();
    protected final Sort sort;
    protected final ImmutableArray<Sort> argSorts;

    protected DLAbstractSortedOperator(Name name,
            ImmutableArray<Sort> argSorts,
            Sort sort,
            ImmutableArray<Boolean> whereToBind,
            boolean isRigid) {

        super(name, argSorts == null ? 0 : argSorts.size(), 
                whereToBind, 
                isRigid);
        assert sort != null;
        this.argSorts = (ImmutableArray<Sort>) 
                (argSorts == null ? EMPTY_SORT_LIST : argSorts);
        this.sort = sort;
    }


    protected DLAbstractSortedOperator(Name name, Sort[] createFormulaSortArray,
            Sort sort, boolean b) {
        this(name, createFormulaSortArray == null ? null : new ImmutableArray<Sort>(createFormulaSortArray), sort, null, b);
    }


    @Override
    public final Sort argSort (int i) {
        return argSorts.get(i);
    }

    @Override
    public final ImmutableArray<Sort> argSorts() {
        return argSorts;
    }

    @Override
    public final Sort sort() {
        return sort;
    }

}