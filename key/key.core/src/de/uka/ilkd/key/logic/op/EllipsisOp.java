package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Operator '...Term...'
 */
public class EllipsisOp extends AbstractSortedOperator{
    protected EllipsisOp(Name name, Sort[] argSorts, Sort sort, boolean isRigid) {
        super(name, argSorts, sort, isRigid);
    }
}
