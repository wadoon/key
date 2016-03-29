package de.uka.ilkd.key.nui.filter;

import java.util.List;

/**
 * A generic criteria that is equivalent to a union operation.
 * 
 * @author Benedikt Gross
 * @version 1.0
 * @param <E>
 */
public class OrCriterion<E> implements Criterion<E> {
    private Criterion<E> _criteria;
    private Criterion<E> _otherCriteria;

    /**
     * Combines the two criteria to a union of the two.
     */
    public OrCriterion(Criterion<E> criteria, Criterion<E> otherCriteria) {
        _criteria = criteria;
        _otherCriteria = otherCriteria;
    }

    @Override
    public List<E> meetCriteria(List<E> entities) {
        List<E> firstCriteriaItems = _criteria.meetCriteria(entities);
        List<E> otherCriteriaItems = _otherCriteria.meetCriteria(entities);

        for (E otherCriteriaItem : otherCriteriaItems) {
            if (!firstCriteriaItems.contains(otherCriteriaItem))
                firstCriteriaItems.add(otherCriteriaItem);
        }

        return firstCriteriaItems;
    }
}