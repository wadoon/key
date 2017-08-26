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
public class AlgorithmicDebugFalseAnnotationType extends AbstractSEAnnotationType {
   /**
    * The ID of this annotation type.
    */
   public static final String TYPE_ID = "org.key_project.sed.core.annotationType.AlgorithmicDebugFalse";

   @Override
   public String getTypeId() {
      // TODO Auto-generated method stub
      return TYPE_ID;
   }

   @Override
   public String getName() {
      return "AlgorithmicDebugFalse";
   }

   @Override
   public boolean isDefaultHighlightBackground() {
      return true;
   }

   @Override
   public RGB getDefaultBackgroundColor() {
      return new RGB(255, 255, 0); //yellow
   }

   @Override
   public boolean isDefaultHighlightForeground() {
      // TODO Auto-generated method stub
      return false;
   }

   @Override
   public RGB getDefaultForegroundColor() {
      return new RGB(255, 255, 0); 
   }

   @Override
   public ISEAnnotation createAnnotation() {
      return new AlgorithmicDebugFalseAnnotation();
   }

   @Override
   public ISEAnnotationLink createLink(ISEAnnotation source, ISENode target) {
      // TODO Auto-generated method stub
      return new AlgorithmicDebugFalseAnnotationLink(source, target);
   }
   
//   @Override
//   public String saveAnnotation(ISEAnnotation annotation) {
//      Assert.isTrue(annotation instanceof AlgorithmicDebugCorrectAnnotation);
//      return 
//   }
//
//   @Override
//   public void restoreAnnotation(ISEAnnotation annotation, String savedContent) {
//      Assert.isTrue(annotation instanceof AlgorithmicDebugCorrectAnnotation);
//      ((AlgorithmicDebugCorrectAnnotation)annotation).setCommentType(savedContent);
//   }
  
   @Override
   public String saveAnnotationLink(ISEAnnotationLink link) {
      Assert.isTrue(link instanceof AlgorithmicDebugFalseAnnotationLink);
      return "AlgorithmicDebugFalse";
   }

//   @Override
//   public void restoreAnnotationLink(ISEAnnotationLink link, String savedContent) {
//      Assert.isTrue(link instanceof AlgorithmicDebugCorrectAnnotationLink);
//      ((AlgorithmicDebugCorrectAnnotationLink)link);
//   }

}
