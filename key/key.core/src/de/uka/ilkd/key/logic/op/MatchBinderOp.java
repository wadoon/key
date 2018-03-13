package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.BottomSort;
import de.uka.ilkd.key.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * BinaryOperator Term : ?rt
 */
public class MatchBinderOp extends Function implements SortedOperator{

    public MatchBinderOp(Name name, ImmutableArray<Sort> argSorts) {
        super(name, argSorts.get(0), argSorts);
        assert argSorts.size() == 1;
    }

    public MatchBinderOp(Name name, Sort binderSort, ImmutableArray<Sort> argSorts ){
        super(name, binderSort, argSorts);
    }
}
