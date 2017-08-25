package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.util.SEAnnotationUtil;

/**
 *  * @author Peter Schauberger
 * 
 */
public class AlgorithmicDebugBugAnnotation extends AbstractSEAnnotation {
   
   public AlgorithmicDebugBugAnnotation() {
      super(SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugBugAnnotationType.TYPE_ID), true);
   }

   @Override
   public boolean canDelete(ISEDebugTarget target) {
      return false;
   }
   
   @Override
   public String toString() {
      return "Correct";
   }
}
