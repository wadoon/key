package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * BinaryOperator Term : ?rt
 */
public class MatchBinderOp extends Function implements SortedOperator{


    /**
     * A match binder operator is for bding an matched inner term to a schmeavariable for termmatching in PSDBG
     * @param name
     * @param binderSort
     * @param argSorts
     */
    public MatchBinderOp(Name name, Sort binderSort, ImmutableArray<Sort> argSorts ){
        super(name, binderSort, argSorts);
        assert argSorts.size() == 2;
        assert binderSort.equals( argSorts.get(0));
    }
}