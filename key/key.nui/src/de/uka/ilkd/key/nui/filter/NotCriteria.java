package de.uka.ilkd.key.nui.filter;

import java.util.List;

public class NotCriteria<E> implements Criteria<E>
{
   private Criteria<E> criteria;

   public NotCriteria(Criteria<E> x)
   {
      criteria = x;
   }

   public Criteria<E> getChildCriteria(){
       return criteria;
   }
   
   public List<E> meetCriteria(List<E> entities)
   {
      List<E> notCriteriaItems = criteria.meetCriteria(entities);
      // ensure original list is not modified, otherwise compound Or will use an already filtered list
      List<E> notEntities = entities;  

      for (E notCriteriaItem : notCriteriaItems)
      {
         notEntities.remove(notCriteriaItem);
      }

      return notEntities;
   }
}