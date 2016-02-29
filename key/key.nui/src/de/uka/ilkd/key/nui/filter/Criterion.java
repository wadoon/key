package de.uka.ilkd.key.nui.filter;

import java.util.List;

/**
 * Base class for all criteria.
 * 
 * @author Benedikt Gross
 *
 * @param <E>
 */
public interface Criterion<E> {
    List<E> meetCriteria(List<E> entities);
}
