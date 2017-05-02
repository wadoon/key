/**
 * 
 */
package org.key_project.sed.core.annotation.impl;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISENode;

/**
 * @author Peter Schauberger
 *
 */
public class HighlightAnnotationLink extends AbstractSEAnnotationLink {
   
   public HighlightAnnotationLink(ISEAnnotation source, ISENode target) {
      super(source, target);
   }

   @Override
   public boolean canDelete() {
      return true;
   }

   @Override
   public void delete() {
      // Remove link
      super.delete();
      // Remove annotation if no links are available
      if (!getSource().hasLinks()) {
         getTarget().getDebugTarget().unregisterAnnotation(getSource());
      }
   }
   
   @Override
   public String toString() {
      String name = "";
      try {
         name = getTarget().getName();
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      return name;
   }
   
   /**
    * Computes a unique HashCode to compare two HighlightAnnotationLinks
    * @author Peter Schauberger
    * @return: a unique HashCode of type int
    */
   @Override
   public int hashCode(){
      int result = 59; //Prime number
      
      return result * ( this.getTarget().hashCode() + this.getSource().hashCode() );
   }
   
   /**
    * Compares two HighlightAnnotationLinks
    * @author Peter Schauberger
    * @param o: the Link that should be compared with this one
    * @return: true if the HighlightAnnotationLinks are equal, false if they are not equal
    */
   @Override
   public boolean equals( Object o )
   {
     if ( o == null )
       return false;
     
     if ( !(o instanceof HighlightAnnotationLink) )
        return false;
     
     HighlightAnnotationLink that = (HighlightAnnotationLink) o;
     
     return this.getSource() == that.getSource() && this.getTarget() == that.getTarget();
   }
   
}
