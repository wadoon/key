package de.uka.ilkd.key.nui.filter;

import java.util.List;

import de.uka.ilkd.key.util.Pair;

public class CriterionEmpty<T> implements Criteria<T> {

    @Override
    public List<T> meetCriteria(List<T> entities) {
        return entities;
    }

}
