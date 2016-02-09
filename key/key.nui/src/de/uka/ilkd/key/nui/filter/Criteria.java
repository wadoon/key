package de.uka.ilkd.key.nui.filter;

import java.util.List;

public interface Criteria<E>
{
   List<E> meetCriteria(List<E> entities); 
}
