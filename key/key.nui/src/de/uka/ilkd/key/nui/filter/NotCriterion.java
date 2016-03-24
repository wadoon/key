package de.uka.ilkd.key.nui.filter;

import java.util.List;

/**
 * A generic criteria that meets the exact opposite of the child criterion.
 * 
 * @author Benedikt Gross
 * @version 1.0
 * @param <E>
 */
public class NotCriterion<E> implements Criterion<E> {
    private Criterion<E> criteria;

    // TODO add documentation
    public NotCriterion(Criterion<E> childCriteria) {
        criteria = childCriteria;
    }

    // TODO add documentation
    public List<E> meetCriteria(List<E> entities) {
        List<E> notCriteriaItems = criteria.meetCriteria(entities);
        // ensure original list is not modified, otherwise compound Or will use
        // an already filtered list
        List<E> notEntities = entities;

        for (E notCriteriaItem : notCriteriaItems) {
            notEntities.remove(notCriteriaItem);
        }

        return notEntities;
    }
}