package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.util.SEAnnotationUtil;

/**
 *  * @author Peter Schauberger
 * 
 */
public class AlgorithmicDebugFalseAnnotation extends AbstractSEAnnotation {
   private static final String DEFAULT_ALGORITHMIC_DEBUG_FALSE = "False";
   /**
    * The type of comments.
    */
   private String commentType = DEFAULT_ALGORITHMIC_DEBUG_FALSE;
   
   /**
    * Constructor.
    */
   public AlgorithmicDebugFalseAnnotation() {
      super(SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugFalseAnnotationType.TYPE_ID), true);
   }

   @Override
   public boolean canDelete(ISEDebugTarget target) {
      // TODO Auto-generated method stub
      return false;
   }
   
   @Override
   public String toString() {
      return "False";
   }
}
