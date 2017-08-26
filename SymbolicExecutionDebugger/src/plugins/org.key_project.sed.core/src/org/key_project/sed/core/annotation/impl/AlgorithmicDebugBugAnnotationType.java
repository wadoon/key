/**
 * 
 */
package org.key_project.sed.core.annotation.impl;

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISENode;

/**
 * @author Peter Schauberger
 *
 */
public class AlgorithmicDebugBugAnnotationType extends AbstractSEAnnotationType {
   /**
    * The ID of this annotation type.
    */
   public static final String TYPE_ID = "org.key_project.sed.core.annotationType.AlgorithmicDebugBug";

   @Override
   public String getTypeId() {
      return TYPE_ID;
   }

   @Override
   public String getName() {
      return "AlgorithmicDebugBug";
   }

   @Override
   public boolean isDefaultHighlightBackground() {
      return true;
   }

   @Override
   public RGB getDefaultBackgroundColor() {
      return new RGB(255, 0, 0); //red
   }

   @Override
   public boolean isDefaultHighlightForeground() {
      return false;
   }

   @Override
   public RGB getDefaultForegroundColor() {
      return new RGB(255, 255, 0);
   }

   @Override
   public ISEAnnotation createAnnotation() {
      return new AlgorithmicDebugBugAnnotation();
   }

   @Override
   public ISEAnnotationLink createLink(ISEAnnotation source, ISENode target) {
      return new AlgorithmicDebugBugAnnotationLink(source, target);
   }
   
//   @Override
//   public String saveAnnotation(ISEAnnotation annotation) {
//      Assert.isTrue(annotation instanceof AlgorithmicDebugBugAnnotation);
//      return 
//   }
//
//   @Override
//   public void restoreAnnotation(ISEAnnotation annotation, String savedContent) {
//      Assert.isTrue(annotation instanceof AlgorithmicDebugBugAnnotation);
//      ((AlgorithmicDebugBugAnnotation)annotation).setCommentType(savedContent);
//   }
  
   @Override
   public String saveAnnotationLink(ISEAnnotationLink link) {
      Assert.isTrue(link instanceof AlgorithmicDebugBugAnnotationLink);
      return "AlgorithmicDebugBug";
   }

//   @Override
//   public void restoreAnnotationLink(ISEAnnotationLink link, String savedContent) {
//      Assert.isTrue(link instanceof AlgorithmicDebugBugAnnotationLink);
//      ((AlgorithmicDebugBugAnnotationLink)link);
//   }

}
