package org.key_project.common.core.logic.op;

import org.key_project.common.core.logic.DLSort;
import org.key_project.common.core.logic.Name;
import org.key_project.util.collection.ImmutableArray;

public abstract class DLAbstractSortedOperator<S extends DLSort>
        extends DLAbstractOperator implements DLSortedOperator<S> {

    @SuppressWarnings("rawtypes")
    protected static final ImmutableArray<?> EMPTY_SORT_LIST = new ImmutableArray();
    protected final S sort;
    protected final ImmutableArray<S> argSorts;

    @SuppressWarnings("unchecked")
    protected DLAbstractSortedOperator(Name name,
            ImmutableArray<S> argSorts,
            S sort,
            ImmutableArray<Boolean> whereToBind,
            boolean isRigid) {
        
        super(name, argSorts == null ? 0 : argSorts.size(), 
                    whereToBind, 
                    isRigid);
        assert sort != null;
        this.argSorts = (ImmutableArray<S>) 
                (argSorts == null ? EMPTY_SORT_LIST : argSorts);
        this.sort = sort;
    }


    @Override
    public final S argSort(int i) {
    return argSorts.get(i);
    }

    @Override
    public final ImmutableArray<S> argSorts() {
    return argSorts;
    }

    @Override
    public final S sort() {
    return sort;
    }

}