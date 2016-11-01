package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEBranchStatement;
import org.key_project.sed.core.model.ISENode;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotation;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationType;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugFalseAnnotation;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugFalseAnnotationType;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

public class AlgorithmicDebugCorrectAnnotationLinkAction implements ISEAnnotationLinkAction {
   
   private ISEAnnotationType annotationTypeCorrect;
   private ISEAnnotationType annotationTypeFalse;
   
   private ISEAnnotation[] registeredAnnotationsCorrect;
   private ISEAnnotation[] registeredAnnotationsFalse;
   
   /**
    * @author Peter Schauberger
    */
   @Override
   public void run(Shell shell, ISENode node) {
      
      this.annotationTypeCorrect = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID);
      this.annotationTypeFalse = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugFalseAnnotationType.TYPE_ID);
      this.registeredAnnotationsCorrect = node.getDebugTarget().getRegisteredAnnotations(annotationTypeCorrect);
      this.registeredAnnotationsFalse = node.getDebugTarget().getRegisteredAnnotations(annotationTypeFalse);
//      
//      Assert.isNotNull(node);
//      Assert.isNotNull(annotationTypeCorrect);
      
    
    ISEAnnotation annotationCorrect = ArrayUtil.search(registeredAnnotationsCorrect, new IFilter<ISEAnnotation>() {
       @Override
       public boolean select(ISEAnnotation element) {
          return element instanceof AlgorithmicDebugCorrectAnnotation; 
       }
    });
      
      if(annotationCorrect == null){
         ISEDebugTarget target = node.getDebugTarget();
         annotationCorrect = annotationTypeCorrect.createAnnotation();
         target.registerAnnotation(annotationCorrect);
      }

      //If AnnotationLink was not found, we create a new one and attach it to the node
        if(node.getAnnotationLinks(annotationTypeCorrect).length == 0){
           if(node.getAnnotationLinks(annotationTypeFalse).length == 0){
  
              node.addAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
             // annotateNext(shell, node);
              }
           else{
              ISEAnnotation annotationFalse = ArrayUtil.search(registeredAnnotationsFalse, new IFilter<ISEAnnotation>() {
                 @Override
                 public boolean select(ISEAnnotation element) {
                    return element instanceof AlgorithmicDebugFalseAnnotation; 
                 }
              });
              node.removeAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
              node.addAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
             //annotateNext(shell, node);
           }
        }
//        else{
//         MessageBox mb = new MessageBox(shell);
//         mb.setText("Hint");
//         mb.setMessage("Node already marked as correct");
//         mb.open();
//        }
   }
   
   /**
    * @author Peter Schauberger
    * @throws DebugException 
    */
   private void annotateNext(Shell shell, ISENode node){
      try {
         ISENode parent = node.getParent();
             
         if(!(parent instanceof ISEBranchStatement))
            run (shell, parent);
            
         else{
            boolean childNotCorrect = false;
            for(ISENode child : parent.getChildren()){
              if(child.getAnnotationLinks(annotationTypeCorrect).length == 0) {
                  childNotCorrect = true;              
                  break;
               }
            }
            if(!childNotCorrect)
               run (shell, parent);              
         }
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      }
}