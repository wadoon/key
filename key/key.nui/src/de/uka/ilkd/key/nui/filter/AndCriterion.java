package de.uka.ilkd.key.nui.filter;

import java.util.List;

/**
 * A generic criterion that is equivalent to an intersection operation.
 * 
 * @author Benedikt Gross
 * @version 1.0
 * @param <E>
 */
public class AndCriterion<E> implements Criterion<E> {
    private Criterion<E> _criteria;
    private Criterion<E> _otherCriteria;

    /**
     * Combines the two criteria to an intersection of the two.
     */
    public AndCriterion(Criterion<E> criteria, Criterion<E> otherCriteria) {
        _criteria = criteria;
        _otherCriteria = otherCriteria;
    }

    @Override
    public List<E> meetCriteria(List<E> entities) {
        List<E> result = _criteria.meetCriteria(entities);
        // If it returns 1 is because only 1 met the criterion
        // and the inherited ands are not executed
        // If it returns 0 is because none met the criterion
        // and the inherited ands are not executed

        if (result.size() == 0 /* Bug :|| result.Count == 1 */ )
            return result;

        return _otherCriteria.meetCriteria(result);
    }
}