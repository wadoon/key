package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISENode;
import org.eclipse.core.runtime.Assert;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugFalseAnnotation;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugFalseAnnotationLink;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugFalseAnnotationType;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotation;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationLink;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationType;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

public class AlgorithmicDebugFalseAnnotationLinkAction implements ISEAnnotationLinkAction {
   
   private ISEAnnotationType annotationTypeFalse;
   private ISEAnnotationType annotationTypeCorrect;
   
   private ISEAnnotation[] registeredAnnotationsFalse;
   private ISEAnnotation[] registeredAnnotationsCorrect;
   /**
    * @author Peter Schauberger
    */
   @Override
   public void run(Shell shell, ISENode node) {
      //TODO: Hier muss die Annotation erzeugt und registriert werden
      
      this.annotationTypeFalse = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugFalseAnnotationType.TYPE_ID);
      this.annotationTypeCorrect = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID);
      this.registeredAnnotationsFalse = node.getDebugTarget().getRegisteredAnnotations(annotationTypeFalse);
      this.registeredAnnotationsCorrect = node.getDebugTarget().getRegisteredAnnotations(annotationTypeCorrect);
      
//      Assert.isNotNull(node);
//      Assert.isNotNull(annotationTypeFalse);
      
      ISEDebugTarget target = node.getDebugTarget();
      ISEAnnotation annotationFalse = ArrayUtil.search(registeredAnnotationsFalse, new IFilter<ISEAnnotation>() {
           @Override
           public boolean select(ISEAnnotation element) {
              return element instanceof AlgorithmicDebugFalseAnnotation; 
           }
        });
      if (annotationFalse == null){
         annotationFalse = annotationTypeFalse.createAnnotation();
         target.registerAnnotation(annotationFalse);}
      
      ISEAnnotation annotationCorrect = ArrayUtil.search(registeredAnnotationsCorrect, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugCorrectAnnotation; 
         }
      });
        
      if (annotationCorrect == null){
         annotationCorrect = annotationTypeCorrect.createAnnotation();
         target.registerAnnotation(annotationCorrect);}

      //If AnnotationLink was not found, we create a new one and attach it to the node
        if(node.getAnnotationLinks(annotationTypeFalse).length == 0){
           if(annotationCorrect == null || node.getAnnotationLinks(annotationTypeCorrect).length == 0){
              
//              MessageBox mb = new MessageBox(shell);
//              mb.setText("Hint");
//              mb.setMessage("Correct Annotation nicht gefunden, markiere False");
//              mb.open();
              node.addAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
              }
           else{
//              MessageBox mb = new MessageBox(shell);
//              mb.setText("Hint");
//              mb.setMessage("Node already marked as Correct. Toggle annotation to False");
//              mb.open();
             
              node.removeAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
              node.addAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
           }
        }
        else{
         node.removeAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
           
         MessageBox mb = new MessageBox(shell);
         mb.setText("Hint");
         mb.setMessage("Node already marked as False");
         mb.open();
        }
   }
}