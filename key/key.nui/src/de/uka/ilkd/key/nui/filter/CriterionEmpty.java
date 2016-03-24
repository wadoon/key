package de.uka.ilkd.key.nui.filter;

import java.util.List;

/**
 * Represents an empty criterion that meets any element in the entities list. Use
 * this for not set criterion variables instead of null.
 * 
 * @author Benedikt Gross
 * @version 1.0
 * @param <T>
 */
public class CriterionEmpty<T> implements Criterion<T> {

    @Override
    public List<T> meetCriteria(List<T> entities) {
        return entities;
    }

}
