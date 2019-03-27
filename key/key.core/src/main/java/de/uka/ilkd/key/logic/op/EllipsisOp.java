package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.BottomSort;
import de.uka.ilkd.key.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * Operator '...Term...'
 */
public class EllipsisOp extends AbstractSortedOperator{


    public EllipsisOp(Sort argSort) {
        super(new Name("..."), new ImmutableArray<>(argSort), BottomSort.INSTANCE, false);
    }
}