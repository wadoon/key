package de.uka.ilkd.key.nui.filter;

import java.util.List;

/**
 * Represents an empty criteria that meets any element in the entities list. Use
 * this for not set criteria variables instead of null.
 * 
 * @author Benedikt Gross
 *
 * @param <T>
 */
public class CriterionEmpty<T> implements Criteria<T> {

    @Override
    public List<T> meetCriteria(List<T> entities) {
        return entities;
    }

}
