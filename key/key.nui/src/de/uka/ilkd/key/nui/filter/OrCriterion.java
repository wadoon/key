package de.uka.ilkd.key.nui.filter;

import java.util.List;

/**
 * A generic criteria that is equivalent to a union operation
 * @author Benedikt Gross
 *
 * @param <E>
 */
public class OrCriterion<E> implements Criterion<E>
{
   private Criterion<E> _criteria;
   private Criterion<E> _otherCriteria;

   public OrCriterion(Criterion<E> criteria, Criterion<E> otherCriteria)
   {
      _criteria = criteria;
      _otherCriteria = otherCriteria;
   }

   public List<E> meetCriteria(List<E> entities)
   {
      List<E> firstCriteriaItems = _criteria.meetCriteria(entities);
      List<E> otherCriteriaItems = _otherCriteria.meetCriteria(entities);
    
      for(E otherCriteriaItem : otherCriteriaItems)
      {
         if(!firstCriteriaItems.contains(otherCriteriaItem))
            firstCriteriaItems.add(otherCriteriaItem);
      }
     
      return firstCriteriaItems;
   }
}