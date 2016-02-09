package de.uka.ilkd.key.nui.filter;

import java.util.List;

public class AndCriteria<E> implements Criteria<E>
{
   private Criteria<E> _criteria;
   private Criteria<E> _otherCriteria;
  
   public AndCriteria(Criteria<E> criteria, Criteria<E> otherCriteria)
   {
      _criteria = criteria;
      _otherCriteria = otherCriteria;
   }

   public List<E> meetCriteria(List<E> entities)
   {
      List<E> result = _criteria.meetCriteria(entities);
      // If it returns 1 is because only 1 met the criterion
      // and the inherited ands are not executed
      // If it returns 0 is because none met the criterion
      // and the inherited ands are not executed

      if (result.size() == 0 /* Bug :|| result.Count == 1*/ )
         return result;
      
      return _otherCriteria.meetCriteria(result);
   }
}