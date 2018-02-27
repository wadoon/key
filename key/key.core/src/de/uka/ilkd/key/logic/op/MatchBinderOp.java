package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * BinaryOperator Term : ?rt
 */
public class MatchBinderOp extends AbstractSortedOperator{

    protected MatchBinderOp(Name name, ImmutableArray<Sort> argSorts, Sort sort, boolean isRigid) {
        super(name, argSorts, sort, isRigid);
    }
}
